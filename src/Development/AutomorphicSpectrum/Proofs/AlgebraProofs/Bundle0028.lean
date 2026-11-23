module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeBaseChangeFree
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeSecondGoodness
section
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

private theorem loc_free_base_change {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω]
    [Algebra o C] [Algebra Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C)
    (hRC : ∀ a ∈ R, algebraMap Ω C a ∈ RC) {ι : Type} [Finite ι] {r : ℕ}
    {L : AddSubgroup (ι → Ω)} (hL : LocFree R r L) :
    LocFree RC r (spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω)))) := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hb⟩ := hL
  refine ⟨fun a ha e he => SpanExact.smul_mem_spanOver RC _ ha he, k,
    fun l => algebraMap Ω C (f l), fun l => algebraMap Ω C (c l), fun l => hRC _ (hf l),
    fun l => hRC _ (hc l), ?_, fun l => ?_⟩
  · have h := congrArg (algebraMap Ω C) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, map_one] using h
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  have hbc := isBaseChange_bcMap Ω C ι
  let B : Module.Basis (Fin r) Ω (ι → Ω) := Module.Basis.mk hli hsp.ge
  let B' := hbc.basis B
  have hB' : (⇑B' : Fin r → ι → C) = fun q => bcMap Ω C ι (b q) := by
    funext q
    simp [B', B, IsBaseChange.basis_apply, Module.Basis.mk_apply]
  have hbl : ∀ q, ∃ m : ℕ, f l ^ m • b q ∈ L := fun q =>
    (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      rcases eq_or_ne q' q with rfl | h
      · simp [one_mem]
      · simp [Pi.single_apply, h]⟩, by simp [Pi.single_apply]⟩
  refine ⟨fun q => bcMap Ω C ι (b q), by rw [← hB']; exact B'.linearIndependent,
    by rw [← hB']; exact B'.span_eq, fun e => ?_⟩
  beta_reduce
  by_cases hg : f l = 0
  · have hg' : algebraMap Ω C (f l) = 0 := by rw [hg, map_zero]
    constructor
    · intro _
      refine ⟨B'.repr e, fun q => ⟨1, by rw [hg', pow_one, zero_mul]; exact zero_mem _⟩, ?_⟩
      conv_lhs => rw [← B'.sum_repr e]
      rw [hB']
    · intro _
      exact ⟨1, by rw [hg', pow_one, zero_smul]; exact zero_mem _⟩
  have hg' : algebraMap Ω C (f l) ≠ 0 := (map_ne_zero _).2 hg
  have hgR : algebraMap Ω C (f l) ∈ RC := hRC _ (hf l)
  constructor
  · rintro ⟨m, hm⟩
    have key : ∀ x ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))), ∃ a : Fin r → C,
        (∀ q, ∃ n : ℕ, algebraMap Ω C (f l) ^ n * a q ∈ RC) ∧
          x = ∑ q, a q • bcMap Ω C ι (b q) := by
      intro x hx
      unfold spanOver at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, y, ⟨v, hv, rfl⟩, rfl⟩ := hx
        obtain ⟨av, hav, rfl⟩ := (hiff v).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
        refine ⟨fun q => a * algebraMap Ω C (av q), fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := hav q
          exact ⟨n, by rw [mul_left_comm, ← map_pow, ← map_mul]; exact mul_mem ha (hRC _ hn)⟩
        · set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul, Finset.smul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← algebraMap_smul C (av q), smul_smul]
      | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        refine ⟨a + a', fun q => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
        obtain ⟨n, hn⟩ := ha q
        obtain ⟨n', hn'⟩ := ha' q
        refine ⟨n + n', ?_⟩
        have h2 : algebraMap Ω C (f l) ^ (n + n') * (a + a') q =
            algebraMap Ω C (f l) ^ n' * (algebraMap Ω C (f l) ^ n * a q) +
              algebraMap Ω C (f l) ^ n * (algebraMap Ω C (f l) ^ n' * a' q) := by
          rw [Pi.add_apply]; ring
        rw [h2]
        exact add_mem (mul_mem (pow_mem hgR _) hn) (mul_mem (pow_mem hgR _) hn')
      | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, fun q => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by rw [Pi.neg_apply, mul_neg]; exact neg_mem hn⟩
    obtain ⟨a, ha, hae⟩ := key _ hm
    refine ⟨fun q => (algebraMap Ω C (f l) ^ m)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨n, hn⟩ := ha q
      refine ⟨n + m, ?_⟩
      rw [pow_add, mul_assoc, ← mul_assoc (algebraMap Ω C (f l) ^ m),
        mul_inv_cancel₀ (pow_ne_zero _ hg'), one_mul]
      exact hn
    · have he : e = (algebraMap Ω C (f l) ^ m)⁻¹ • (algebraMap Ω C (f l) ^ m • e) := by
        rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg'), one_smul]
      rw [he, hae, Finset.smul_sum]
      simp only [smul_smul]
  · rintro ⟨a, ha, rfl⟩
    choose na hna using ha
    choose mb hmb using hbl
    refine ⟨∑ q, na q + ∑ q, mb q, ?_⟩
    rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun q _ => ?_
    have h1 : na q ≤ ∑ q, na q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have h2 : mb q ≤ ∑ q, mb q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have e1 : algebraMap Ω C (f l) ^ (∑ q, na q + ∑ q, mb q) =
        algebraMap Ω C (f l) ^ (∑ q, na q - na q) * algebraMap Ω C (f l) ^ na q *
          (algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * algebraMap Ω C (f l) ^ mb q) := by
      rw [← pow_add, ← pow_add, ← pow_add, Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
    have hcoef : algebraMap Ω C (f l) ^ (∑ q, na q - na q) *
        algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q) ∈ RC :=
      mul_mem (mul_mem (pow_mem hgR _) (pow_mem hgR _)) (hna q)
    have hmem : (algebraMap Ω C (f l) ^ (∑ q, na q - na q) *
        algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q)) •
          bcMap Ω C ι (f l ^ mb q • b q) ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))) :=
      AddSubgroup.subset_closure ⟨_, hcoef, _, ⟨_, hmb q, rfl⟩, rfl⟩
    convert hmem using 1
    rw [map_smul, ← algebraMap_smul C (f l ^ mb q), smul_smul, smul_smul, map_pow, e1]
    congr 1
    ring

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → (∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) ∧ ∀ i, LocFree R 1 (D.dId R p (χ τ) i) ∧ LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₂ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.kerH R p τ (χ τ)) ∧ ∀ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) ∧ ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG1 hG2 haf
  obtain ⟨hdL, hdB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main D R p w χ hc hB hG1 hG2
  obtain ⟨hsL, hsB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.stepKer D R p w χ hc hB hG1 hG2
  have hkL := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main D R p w χ hc hB hG1 hG2 haf
  have h68 := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hc hB hG1
  refine ⟨fun τ => ⟨hkL τ, fun i => ⟨hdL τ i, hsL τ i⟩⟩, ?_⟩
  intro C _ _ _ _ RC hRC
  have hbc := h68.2 C RC hRC
  have h69 := _root_.GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change D R p w χ hc hB hG1 C RC hRC
  have h70 := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange.imH_bc D R p w χ hc hB hG1 haf C RC hRC
  refine ⟨⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_, fun τ => ?_⟩,
    fun τ => ⟨_root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC.main D R p w χ hc hB hG1 hG2 haf C RC hRC τ,
      fun i => ⟨hdB C RC hRC τ i, hsB C RC hRC τ i⟩⟩⟩
  · beta_reduce
    rw [(hbc.2 τ).1, ← span_bcMap_annSub Ω C n i]
    exact (_root_.GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C (Fin n))
      (D.af R p (χ τ)) (annSub Ω n i) (h68.1 τ).1.1 (hG2.ann τ i)).1
  · rw [(h69 τ).1 i]
    exact loc_free_base_change R RC hRC (hG2.kk τ i)
  · beta_reduce
    rw [(h69 τ).2 i,
      show AddMonoidHom.snd C (Fin (r τ) → C) = (LinearMap.snd C C (Fin (r τ) → C)).toAddMonoidHom
        from rfl, SpanExact.map_spanOver]
    have himg : (LinearMap.snd C C (Fin (r τ) → C)) ''
        (Prod.map (algebraMap Ω C) (bcMap Ω C (Fin (r τ))) '' (D.stepGraph τ (χ τ) i : Set _)) =
          bcMap Ω C (Fin (r τ)) ''
            ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd Ω (Fin (r τ) → Ω)) : Set _) := by
      rw [AddSubgroup.coe_map, Set.image_image, Set.image_image]
      rfl
    rw [himg]
    exact loc_free_base_change R RC hRC (hG2.step τ i)
  · beta_reduce
    rw [h70 τ]
    exact loc_free_base_change R RC hRC (hG2.im τ)

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeMonoInjectiveHom
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_map_of_injective : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) :=
  PositivityTheory.HtPt.Ch.deg_inj

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeNonposTrivialLattice
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_zero_of_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 :=
  @PositivityTheory.HtPt.Ch.subdeg_trivial

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFiniteStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : TorsRep G p) (N : Type) [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → Finite N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.tors_pts_finite | exact GlobalTheory.CompanionTheory.Ar.GR.tors_pts_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.tors_pts_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsIsogenyHopfOrder
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ _ _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj
  haveI := hj
  have hex : ∀ x : N, ∃ y : N', pt' y = pt x ≫ j := by
    intro x
    apply (hpt'.range _).1
    have hx : (pt x) ^ p = 1 := (hpt.range _).2 ⟨x, rfl⟩
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  choose f hf using hex
  have hadd : ∀ x y : N, f (x + y) = f x + f y := by
    intro x y
    apply hpt'.inj
    rw [hpt'.add, hf, hf, hf, hpt.add, MonObj.mul_comp]
  let jN : N →+ N' :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        simpa using h.symm
      map_add' := hadd }
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  refine ⟨jN, ψ, fun x => hf x, hψ, ?_⟩
  intro g hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨ψ a, ?_⟩
  intro x φ hφ
  have key : spMap (φ.comp ψ) ≫ T'.y = pt' (jN x) := by
    rw [← Chart.spMap_comp ψ φ]
    change (spMap φ ≫ spMap ψ) ≫ T'.y = pt' (f x)
    rw [Category.assoc, hψ, ← Category.assoc, hφ, hf]
  exact ha (jN x) (φ.comp ψ) key
end

