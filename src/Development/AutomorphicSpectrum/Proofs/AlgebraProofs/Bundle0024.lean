module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Avoid
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeImageBaseChange
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

theorem map_snd_spanOver {o C V Z Vc Zc : Type} [CommRing o] [Field C] [Algebra o C]
    (RC : Subalgebra o C) [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (G : AddSubgroup (V × Z)) :
    (spanOver RC (Prod.map b b' '' G)).map (AddMonoidHom.snd Vc Zc) =
      spanOver RC (b' '' G.map (AddMonoidHom.snd V Z)) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, b' y.2, ⟨y.2, AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    exact ⟨a • Prod.map b b' y, ⟨a, ha, Prod.map b b' y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩

theorem hh_le_divLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
    {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (hw : mulLat w (stdLat R _) ≤ D.af R p χ) :
    D.hh R p χ ≤ divLat w (stdLat R (Fin n)) := by
  intro v hv
  change v ∈ dotDual R (D.af R p χ) at hv
  unfold dotDual at hv
  simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
  rw [stdLat, AddSubgroup.mem_pi]
  intro i _
  have he : (Pi.single i (1 : Ω) : Fin n → Ω) ∈ stdLat R (Fin n) := by
    rw [stdLat, AddSubgroup.mem_pi]
    intro j _
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  have hwe : w • (Pi.single i (1 : Ω) : Fin n → Ω) ∈ D.af R p χ :=
    hw (AddSubgroup.mem_map_of_mem (DistribSMul.toAddMonoidHom (Fin n → Ω) w) he)
  have h := AddSubgroup.mem_iInf.mp
    (AddSubgroup.mem_iInf.mp hv (w • (Pi.single i (1 : Ω) : Fin n → Ω))) hwe
  have h2 : (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v ∈ R := h
  have h3 : (w • v) i = (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v := by
    simp [dotProduct, Pi.single_apply]
  show (w • v) i ∈ R
  rw [h3]
  exact h2

theorem imH_bc : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG hw C _ _ _ _ RC hR τ
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨hp, -, ⟨c, -, hpc⟩, -⟩ := hc
    exact hp (by rw [hpc, mul_zero])
  have hfst : (D.Del τ).map (AddMonoidHom.fst _ _) = divLat w (stdLat R (Fin n)) := by
    ext b
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b', c⟩, h, rfl⟩
      exact ((hB.del τ).1 b').mp ⟨c, h⟩
    · intro h
      obtain ⟨c, hcc⟩ := ((hB.del τ).1 b).mpr h
      exact ⟨(b, c), hcc, rfl⟩
  have hstab : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    change v ∈ dotDual R (D.af R p (χ τ)) at hv
    change a • v ∈ dotDual R (D.af R p (χ τ))
    unfold dotDual at hv ⊢
    rw [AddSubgroup.mem_iInf]
    intro l
    rw [AddSubgroup.mem_iInf]
    intro hl
    have h1 : l ⬝ᵥ v ∈ R := AddSubgroup.mem_iInf.mp (AddSubgroup.mem_iInf.mp hv l) hl
    have h2 : l ⬝ᵥ (a • v) = a * (l ⬝ᵥ v) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    show l ⬝ᵥ (a • v) ∈ R
    rw [h2]
    exact R.mul_mem ha h1
  have hhh : (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) :=
    (((_root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hc hB hG).2 C RC hR).2 τ).2.1
  have key := (_root_.GlobalTheory.CompanionTheory.Ar.GraphRestrict.main R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (isBaseChange_bcMap Ω C _) (isBaseChange_bcMap Ω C _) (D.Del τ) (D.hh R p (χ τ)) n
    (fun a ha v hv => (hB.stable τ a ha).2.1 v hv)
    (by rw [hfst]; exact locFree_divLat R hw0 (locFree_stdLat R n))
    (by rw [hfst]; exact hh_le_divLat D R p w (χ τ) (hw τ)) hstab).1
  have hDel : (D.bc RC).Del τ =
      spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' D.Del τ) := rfl
  unfold LieLatticeData.imH
  rw [hhh, hDel, key]
  exact map_snd_spanOver RC _ _ _

end GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOfTwistedDualGens
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat

theorem exists_minor_ne_zero {Ω : Type*} [Field Ω] {M i : ℕ} (A : Fin M → Fin i → Ω)
    (hA : ∀ t : Fin i → Ω, t ∈ Submodule.span Ω (Set.range A)) :
    ∃ I : Fin i → Fin M, Matrix.det (Matrix.of fun a b : Fin i => A (I a) b) ≠ 0 := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent Ω (Set.range A)
  have htop : (⊤ : Submodule Ω (Fin i → Ω)) ≤ Submodule.span Ω (Set.range ((↑) : b → Fin i → Ω)) := by
    rw [Subtype.range_coe, hspan]
    exact fun t _ => hA t
  let bas := Module.Basis.mk hli htop
  have e : b ≃ Fin i := bas.indexEquiv (Pi.basisFun Ω (Fin i))
  have hI : ∀ a : Fin i, ∃ l, A l = (e.symm a : Fin i → Ω) := fun a => hb (e.symm a).2
  choose I hI using hI
  refine ⟨I, ?_⟩
  have hrow : LinearIndependent Ω (Matrix.of fun a b : Fin i => A (I a) b).row := by
    have : (Matrix.of fun a b : Fin i => A (I a) b).row = ((↑) : b → Fin i → Ω) ∘ e.symm := by
      funext a
      exact hI a
    rw [this]
    exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem chartRing_le_fnField (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) {r : Ω} (hr : r ∈ chartRing O (mseg x) s) :
    r ∈ fnField O x := by
  rw [chartRing] at hr
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    show (∏ k, x ⟨k, t k⟩) / (∏ k, x ⟨k, s k⟩) ∈ fnField O x
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, (t k, s k)⟩, rfl⟩)
  | algebraMap c => exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

theorem mem_span_of_twistedDualGens (E : ChartBundle O (mseg x) N V) {M : ℕ} {a : K → ℤ}
    {φ : Fin M → Module.Dual Ω V} (hg : IsTwistedDualGens x E a φ) {s₀ : ∀ k, ι k}
    (hs : mseg x s₀ ≠ 0) (ψ : Module.Dual Ω V) : ψ ∈ Submodule.span Ω (Set.range φ) := by
  classical
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := E.frame s₀ hs
  have hne : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  obtain ⟨l, hl⟩ := hne
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  let bas := Module.Basis.mk hli hsp.ge
  obtain ⟨kg, G, hG, hgen⟩ := GroundTheory.Heights₂.Heights.Model.chartBundle_exists_gens E hs
  have hcoord : ∀ q, bas.coord q ∈ Submodule.span Ω (Set.range φ) := by
    intro q
    have h1 : ∀ g, ∃ n : ℕ, f l ^ n * bas.coord q (G g) ∈ chartRing O (mseg x) s₀ := by
      intro g
      obtain ⟨a', ha', he⟩ := (hiff (G g)).1 ⟨0, by simpa using hG g⟩
      have : bas.coord q (G g) = a' q := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [he, map_sum]
        simp only [map_smul]
        have hbq : ∀ q', bas.coord q (b q') = if q' = q then 1 else 0 := by
          intro q'
          have : b q' = bas q' := (Module.Basis.mk_apply hli hsp.ge q').symm
          rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        simp [hbq]
      rw [this]
      exact ha' q
    choose n hn using h1
    set n₀ := Finset.univ.sup n with hn₀
    have h2 : ∀ g, f l ^ n₀ * bas.coord q (G g) ∈ chartRing O (mseg x) s₀ := by
      intro g
      have hle : n g ≤ n₀ := Finset.le_sup (Finset.mem_univ g)
      rw [← pow_sub_mul_pow _ hle, mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hn g)
    have h3 : ∀ v ∈ E.lat s₀, (f l ^ n₀ • bas.coord q) v ∈ chartRing O (mseg x) s₀ := by
      intro v hv
      obtain ⟨β, hβ, rfl⟩ := hgen v hv
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine sum_mem fun g _ => ?_
      exact mul_mem (hβ g) (h2 g)
    obtain ⟨u, -, hu⟩ := hg.generate s₀ hs _ h3
    have h4 : f l ^ n₀ • bas.coord q ∈ Submodule.span Ω (Set.range φ) := by
      rw [hu]
      exact sum_mem fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    have h5 := Submodule.smul_mem _ (f l ^ n₀)⁻¹ h4
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul] at h5
  rw [← bas.sum_dual_apply_smul_coord ψ]
  exact sum_mem fun q _ => Submodule.smul_mem _ _ (hcoord q)

theorem exists_flagMinor_ne_zero {M : ℕ} {φ : Fin M → Module.Dual Ω V}
    (hφ : ∀ ψ : Module.Dual Ω V, ψ ∈ Submodule.span Ω (Set.range φ))
    (w : Module.Basis (Fin N) Ω V) (i : ℕ) (hi : i ≤ N) :
    ∃ I : Fin i → Fin M, flagMinor φ w i hi I ≠ 0 := by
  classical
  let L : Module.Dual Ω V →ₗ[Ω] (Fin i → Ω) :=
    LinearMap.pi fun b => Module.Dual.eval Ω V (w (Fin.castLE hi b))
  refine exists_minor_ne_zero (fun l b => φ l (w (Fin.castLE hi b))) fun t => ?_
  let ψ : Module.Dual Ω V := ∑ b, t b • w.coord (Fin.castLE hi b)
  have hL : L ψ = t := by
    funext b
    simp [L, ψ, Module.Dual.eval_apply, Finsupp.single_apply, Fin.castLE_inj]
  have h := Submodule.mem_map_of_mem (f := L) (hφ ψ)
  rw [Submodule.map_span, ← Set.range_comp, hL] at h
  exact h

theorem flagMinor_div_mem (E : ChartBundle O (mseg x) N V) {M : ℕ} {a : K → ℤ}
    {φ : Fin M → Module.Dual Ω V} (hg : IsTwistedDualGens x E a φ) {s₀ : ∀ k, ι k}
    (hs : mseg x s₀ ≠ 0) (w : Module.Basis (Fin N) Ω V)
    (hw : ∀ i, ∃ c : O, algebraMap O Ω c ≠ 0 ∧ algebraMap O Ω c • w i ∈ E.lat s₀)
    (i : ℕ) (hi : i ≤ N) (I I' : Fin i → Fin M) :
    flagMinor φ w i hi I / flagMinor φ w i hi I' ∈ fnField O x := by
  classical
  choose c hc0 hc using hw
  have hr : ∀ l b, ∃ r ∈ chartRing O (mseg x) s₀,
      φ l (algebraMap O Ω (c b) • w b) = r * ∏ k, x ⟨k, s₀ k⟩ ^ a k :=
    fun l b => hg.sections s₀ hs l _ (hc b)
  choose r hrm hr using hr
  set T : Ω := ∏ k, x ⟨k, s₀ k⟩ ^ a k with hT
  let D : Fin i → Ω := fun b => (algebraMap O Ω (c (Fin.castLE hi b)))⁻¹ * T
  have hφw : ∀ l b, φ l (w b) = (algebraMap O Ω (c b))⁻¹ * T * r l b := by
    intro l b
    have := hr l b
    rw [map_smul, smul_eq_mul] at this
    field_simp [hc0 b]
    linear_combination this
  have hdet : ∀ J : Fin i → Fin M, flagMinor φ w i hi J = (∏ b, D b) *
      Matrix.det (Matrix.of fun a' b : Fin i => r (J a') (Fin.castLE hi b)) := by
    intro J
    rw [← Matrix.det_mul_row]
    unfold flagMinor
    congr 1
    ext a' b
    simp [hφw, D]
  have hmem : ∀ J : Fin i → Fin M,
      Matrix.det (Matrix.of fun a' b : Fin i => r (J a') (Fin.castLE hi b)) ∈ fnField O x := by
    intro J
    rw [Matrix.det_apply']
    refine sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun b _ => ?_)
    exact chartRing_le_fnField O x s₀ (hrm _ _)
  rw [hdet I, hdet I']
  by_cases hD : ∏ b, D b = 0
  · simp [hD, zero_mem]
  · rw [mul_div_mul_left _ _ hD]
    exact div_mem (hmem I) (hmem I')

end GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat

open GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat in
theorem GlobalTheory.CompanionTheory.Ar.Num.plucker_birat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (J : Type) [Fintype J] [DecidableEq J] (E : J → ChartBundle O (mseg x) N V) (M : J → ℕ) (a : J → K → ℤ) (φ : ∀ j, Fin (M j) → Module.Dual Ω V), (∀ j, IsTwistedDualGens x (E j) (a j) (φ j)) → ∀ (w : Module.Basis (Fin N) Ω V) (s₀ : ∀ k, ι k), mseg x s₀ ≠ 0 → (∀ k, ∃ I, pluckerCoord φ w ⟨k, I⟩ ≠ 0) ∧ ((∀ j i, ∃ c : O, algebraMap O Ω c ≠ 0 ∧ algebraMap O Ω c • w i ∈ (E j).lat s₀) → fnField O (joinCoord x (pluckerCoord φ w)) = fnField O x) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ J _ _ E M a φ hg w s₀ hs
  refine ⟨fun k => ?_, fun hw => le_antisymm ?_ ?_⟩
  · exact exists_flagMinor_ne_zero (mem_span_of_twistedDualGens (E k.1) (hg k.1) hs) w k.2
      (Nat.lt_succ_iff.mp k.2.2)
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, p, q⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · rcases k with k | k
      · exact Subfield.subset_closure (Or.inr ⟨⟨k, (p, q)⟩, rfl⟩)
      · exact flagMinor_div_mem (E k.1) (hg k.1) hs w (hw k.1) k.2 (Nat.lt_succ_iff.mp k.2.2) p q
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, p, q⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨Sum.inl k, (p, q)⟩, rfl⟩)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactStandardLattice
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem glue_gamdel_graphs : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) :=
  PositivityTheory.HtPt.Gamdel.glue_gamdel

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacterStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_character : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS σ hσ g hg
  have sum_Icc_pow_eq_mul_sum_range (ζ : R) (n : ℕ) :
      ∑ m ∈ Finset.Icc 1 n, ζ ^ m = ζ * ∑ m ∈ Finset.range n, ζ ^ m := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, mul_add, pow_succ']
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have : IsDomain R := Function.Injective.isDomain (algebraMap R C) hinj
  obtain ⟨h0, w, hw⟩ := PositivityTheory.HtPt.Rb.exists_inv_card (F := F) hv hp hc
  have hgA : g ∈ AA.carrier := (Submodule.mem_inf.1 hg).1
  have hg0 : g 0 = 0 := by simpa using LinearMap.mem_ker.1 (Submodule.mem_inf.1 hg).2
  refine ⟨fun χ => ⟨PositivityTheory.HtPt.Rb.proj_mem hw AA.carrier χ g (fun a => hFS a g hgA),
      fun a x => PositivityTheory.HtPt.Rb.proj_smul_apply χ g hg0 a x⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hord, -, -, -, hsep⟩ := FundGen.main p C v R hv hp F f hc σ hσ
    have hcardU : Fintype.card Fˣ = p ^ f - 1 := by rw [Fintype.card_units, hc]
    have hσq : σ ^ (p ^ f - 1) = 1 := hord ▸ pow_orderOf_eq_one σ
    have hz : ∀ a : Fˣ, ∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F) =
        if a = 1 then ((p ^ f - 1 : ℕ) : R) else 0 := by
      intro a
      have hpow : ∀ m : ℕ, (σ ^ m)⁻¹ (a : F) = (σ⁻¹ (a : F)) ^ m := fun m => by
        rw [← inv_pow, MulChar.pow_apply_coe]
      simp only [hpow]
      split_ifs with ha
      · subst ha
        simp
      · have hroot : (σ⁻¹ (a : F)) ^ (p ^ f - 1) = 1 := by
          rw [← MulChar.pow_apply_coe, inv_pow, hσq, inv_one, MulChar.one_apply_coe]
        have hneRoot : σ⁻¹ (a : F) ≠ 1 := by
          intro h1
          have hne : (a : F) ≠ 1 := fun h => ha (Units.val_eq_one.1 h)
          have hs := hsep (a : F) 1 hne
          have hsa : σ (a : F) = 1 := by
            have := PositivityTheory.HtPt.Rb.inv_mul_apply σ a
            rwa [h1, one_mul] at this
          rw [hsa, MulChar.map_one, sub_self, map_zero, map_zero] at hs
          exact zero_ne_one hs
        rw [sum_Icc_pow_eq_mul_sum_range]
        have hgeom := geom_sum_mul (σ⁻¹ (a : F)) (p ^ f - 1)
        rw [hroot, sub_self] at hgeom
        rw [(mul_eq_zero.1 hgeom).resolve_right (sub_ne_zero.2 hneRoot), mul_zero]
    funext x
    have hsum : (∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g) x =
        (Fintype.card Fˣ : C)⁻¹ * ∑ a : Fˣ, algebraMap R C
          (∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F)) * g ((a : F) • x) := by
      rw [Finset.sum_apply]
      simp only [proj]
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
    rw [hsum]
    simp only [hz, apply_ite (algebraMap R C), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Units.val_one, one_smul, map_natCast]
    rw [← hcardU, inv_mul_cancel_left₀ h0]
  · intro haf χ
    have hA : g ∈ AA.carrier := (Submodule.mem_inf.1 haf).1
    have hadd : ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := (Submodule.mem_inf.1 haf).2
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => Submodule.mem_inf.2 ⟨hFS a g hA, fun x y => ?_⟩
    simpa [smul_add] using hadd (a • x) (a • y)
  · intro K hK χ
    obtain ⟨hA, hinv⟩ := hK
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => ⟨hFS a g hA, fun y k hk => ?_⟩
    simp only [smul_add]
    exact hinv (a • y) (a • k) (K.smul_mem a hk)
  · intro hsq χ
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => ?_
    let L : (N → C) →ₗ[R] (N → C) := LinearMap.funLeft R C (fun x : N => a • x)
    have haug (u : N → C) (hu : u ∈ augIdeal AA.carrier) : L u ∈ augIdeal AA.carrier := by
      obtain ⟨huA, hu0⟩ := Submodule.mem_inf.1 hu
      refine Submodule.mem_inf.2 ⟨hFS a u huA, LinearMap.mem_ker.2 ?_⟩
      have huZero : u 0 = 0 := by simpa using LinearMap.mem_ker.1 hu0
      simpa [L, smul_zero] using huZero
    have hle : sqIdeal (augIdeal AA.carrier) ≤ (sqIdeal (augIdeal AA.carrier)).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, u', hu', rfl⟩
      exact Submodule.subset_span ⟨L u, haug u hu, L u', haug u' hu', rfl⟩
    exact hle hsq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupLengthStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_length : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | exact GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerLiftOfEmbedding
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem teichmuller_lift_of_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p :=
  PositivityTheory.HtPt.Teich.glue_teich

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TopAvoid
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem topAvoid : ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.avoid

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFinite
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem tors_pts_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : TorsRep G p) (N : Type) [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → Finite N := by
  intro R _ _ p G _ T N _ pt h
  haveI := T.free
  haveI := T.fin
  have hx : ∀ x, ∃ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x := fun x =>
    (T.univ R (pt x) ((h.range _).2 ⟨x, rfl⟩)).exists
  choose f hf using hx
  refine Finite.of_injective f fun x y e => h.inj ?_
  rw [← hf x, ← hf y, e]

end GlobalTheory.CompanionTheory.Ar.GR
end
end

