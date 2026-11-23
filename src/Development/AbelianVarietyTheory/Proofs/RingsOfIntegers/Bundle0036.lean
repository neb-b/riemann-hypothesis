module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PullMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translT_mul {T : Over S} (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  rw [translT, lift_transl, translPt_eq, translT, translPt_eq, MonObj.comp_mul, _root_.mul_assoc]

theorem translT_one {T : Over S} : translT A (1 : T ⟶ A) = 𝟙 _ := by
  rw [translT, translPt_eq, MonObj.comp_one, _root_.one_mul, lift_fst_snd]

theorem translT_endT (φ : A ⟶ A) [IsMonHom φ] {T : Over S} (x : T ⟶ A) :
    translT A x ≫ endT A T φ = endT A T φ ≫ translT A (x ≫ φ) := by
  rw [lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, MonObj.mul_comp, Category.assoc]

theorem negT_endT (φ : A ⟶ A) [IsMonHom φ] (T : Over S) : negT A T ≫ endT A T φ = endT A T φ ≫ negT A T := by
  rw [negT, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc, lift_snd_assoc]
  exact congrArg _ (GrpObj.inv_comp (snd T A) φ)

theorem negT_translT [IsCommMonObj A] {T : Over S} (x : T ⟶ A) :
    negT A T ≫ translT A x = translT A x⁻¹ ≫ negT A T := by
  rw [negT, lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, GrpObj.comp_inv]
  refine congrArg _ ?_
  show fst T A ≫ x * (snd T A)⁻¹ = ((fst T A ≫ x)⁻¹ * snd T A)⁻¹
  rw [mul_inv, inv_inv]


omit [GrpObj A] in
theorem exists_conj {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (m' m : T ⊗ A ⟶ A) (e : m' ≫ φ = endT A T φ ≫ m)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![b, -b])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m'.left] ![a, -a]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u' r z J = val α (r ≫ (snd T A).left) z J * val u (r ≫ (endT A T φ).left) z J *
          (val α (r ≫ m'.left) z J)⁻¹ := by
  have e₁ : (endT A T φ).left ≫ (snd T A).left = (snd T A).left ≫ φ.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (endT A T φ).left ≫ m.left = m'.left ≫ φ.left := by
    rw [← Over.comp_left, ← e, Over.comp_left]
  obtain ⟨u', hu', hv⟩ := exists_gen hL (φ' := ![(snd T A).left, m'.left]) (ε' := ![a, -a])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ α (snd T A).left)
      (LB.pullGen L _ _ u (endT A T φ).left)) (LB.invGen L _ _ (LB.pullGen L _ _ α m'.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)
      (DVR.pullGen_isGen _ _ _ _ hu _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  refine ⟨u', hu', fun Z r z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

theorem prod_conj {U : Type} [CommGroup U] (f g : ℕ → U) (n N : ℕ)
    (hg : ∀ i, ∏ j ∈ Finset.range n, g (n * i + j) = 1) (hf : f (n * N) = f 0) :
    ∏ j ∈ Finset.range (n * N), (f j * g j * (f (j + 1))⁻¹) = 1 := by
  have t : ∀ k, ∏ j ∈ Finset.range k, (f j * g j * (f (j + 1))⁻¹) =
      f 0 * (∏ j ∈ Finset.range k, g j) * (f k)⁻¹ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      group
  have p : ∀ M, ∏ j ∈ Finset.range (n * M), g j = 1 := fun M => by
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, Finset.prod_range_add, ih, hg, _root_.mul_one]
  rw [t, p, hf, _root_.mul_one, mul_inv_cancel]

theorem exists_symLift_conj [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (n N : ℕ) (x : T ⟶ A) (hx : x ^ (n * N) = 1) (U : ThetaGrp A L b T) (H : SymLift A L b n (x ≫ φ) U) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![a, -a]), ∃ hu : u.IsGen,
      SymLift A L a (n * N) x ⟨x, u, hu⟩ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u r z J = val α (r ≫ (snd T A).left) z J *
          val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
            (r ≫ (endT A T φ).left) z J * (val α (r ≫ (translPt A x).left) z J)⁻¹ := by
  have hp := H.pt_eq
  have ts : ∀ y : T ⟶ A, translT A y ≫ snd T A = translPt A y := fun y => lift_snd _ _
  have ns : negT A T ≫ snd T A = snd T A ≫ (GrpObj.inv : A ⟶ A) := lift_snd _ _
  obtain ⟨u, hu, vu⟩ := exists_conj hL φ a b α hα (translPt A x) (translPt A U.pt) (by
    rw [hp, ← ts (x ≫ φ), ← Category.assoc, ← translT_endT, Category.assoc, lift_snd, ← Category.assoc, ts])
    U.φ U.isGen
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨ν', hν', vν⟩ := exists_conj hL φ a b α hα (snd T A ≫ (GrpObj.inv : A ⟶ A))
    (snd T A ≫ (GrpObj.inv : A ⟶ A)) (by
      rw [lift_snd_assoc]
      exact GrpObj.inv_comp (snd T A) φ) ν hν
  refine ⟨u, hu, ⟨rfl, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, vu⟩
  · refine (ThetaPullback.val_powGen ⟨x, u, hu⟩ (n * N) _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) ((Fin.prod_univ_eq_prod_range _ _).trans (prod_conj
      (fun j => val α (translPt A (x ^ j)).left y J)
      (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
        (endT A T φ ≫ translT A (U.pt ^ j)).left y J) n N (fun i => ?_) (by rw [hx, pow_zero])))
    · refine (vu _ _ y J hJ).trans ?_
      simp only [Category.id_comp, ← Over.comp_left]
      rw [ts, translT_endT, MonObj.pow_comp, ← hp, ← ts x, ← Category.assoc, translT_mul, ts, pow_succ']
    · have e := (ThetaPullback.val_powGen U n (endT A T φ ≫ translT A (U.pt ^ (n * i))).left hJ).symm.trans
        ((val_corr hJ H.pow_eq _).trans (val_one _))
      refine Eq.trans ?_ e
      rw [← Fin.prod_univ_eq_prod_range (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left])
        (ε := ![b, -b]) U.φ (endT A T φ ≫ translT A (U.pt ^ (n * i + j))).left y J)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Over.comp_left, Category.assoc, translT_mul, ← pow_add, add_comm]
  · have e := (ThetaPullback.val_symGen U ν (endT A T φ).left hJ).symm.trans ((val_corr hJ hs _).trans (val_one _))
    refine (ThetaPullback.val_symGen ⟨x, u, hu⟩ ν' _ hJ).trans (Eq.trans ?_ (e.trans (val_one _).symm))
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (vu _ _ y J hJ) (vν _ _ y J hJ))
      (congrArg₂ (· * ·) (vu _ _ y J hJ) (congrArg (·⁻¹) (vν _ _ y J hJ)))).trans ?_
    simp only [Category.id_comp, ← Over.comp_left]
    have e₁ : translT A x⁻¹ ≫ translPt A x = snd T A := by
      rw [← ts x, ← Category.assoc, translT_mul, mul_inv_cancel, translT_one, Category.id_comp]
    have e₂ : negT A T ≫ translPt A x = translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) := by
      rw [← ts x, ← Category.assoc, negT_translT, Category.assoc, ns]
    rw [e₁, e₂, ns, negT_endT, translT_endT, GrpObj.inv_comp, ← hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isSymAct_of_isNormPull [IsCommMonObj A] (hA : IsAbelianScheme A) (L : RigLB A) (φ : A ⟶ A) [IsMonHom φ]
    (k N : ℕ) {T : Over S} (x : T ⟶ A) (hx : x ^ (k * N) = 1) {F G : LB.Sec (LPow A L.L (k : ℤ) T)}
    {F' G' : LB.Sec (LPow A L.L ((k * N : ℕ) : ℤ) T)} (h : IsSymAct A L k (x ≫ φ) F G)
    (hF : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) F F') (hG : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) G G') :
    IsSymAct A L (k * N) x F' G' := by
  have hL := L.isLB
  obtain ⟨-, U, H, ac⟩ := h
  obtain ⟨α₀, α, g₀, n₀, c, tw⟩ := hF
  obtain ⟨α₀', α', g₀', n₀', c', tw'⟩ := hG
  obtain ⟨u, hu, H', vu⟩ := exists_symLift_conj hL φ _ _ α₀ g₀ k N x hx U H
  refine ⟨hx, ⟨x, u, hu⟩, H', VVRank.isTwistPull_of_sv A hL hu fun y J hJ => ?_⟩
  have bb := fun r : (T ⊗ A).left ⟶ A.left =>
    gen_unique hL A.hom (eSec A) (Over.w η[A]) (SemiRigid.globalFns _ _ hA).2 g₀' g₀ (fun w I hI => by
      have a := val_corr hI n₀' (𝟙 _)
      have b := val_corr hI n₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm) _ r y J hJ
  rw [VVRank.sv_of_isTwistPull A tw' _ y hJ, VVRank.sv_of_isTwistPull A tw _ y hJ,
    VVRank.sv_of_isTwistPull A ac _ y hJ, vu _ _ y J hJ, val_corr hJ c, val_corr hJ c', val_pull hJ, val_pull hJ, bb]
  simp only [Category.id_comp, ← Over.comp_left]
  rw [translT_endT, ← H.pt_eq, show translT A x ≫ snd T A = translPt A x from lift_snd _ _,
    ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.PullMove

namespace GlobalTheory.PlaceInt

theorem moves_of_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (β : 𝓞 E) (N k k' : ℕ), β * H.bar β = (N : 𝓞 E) → k' = k * N → Odd k' → ∀ (b b' : (ptO Xo x ⟶ Xo.univ.t.G)), b' ≫ Xo.univ.t.act.act β = b → b' ^ k' = 1 → ∀ (F G : SecN Xo x k) (F' G' : SecN Xo x k'), Moves Xo b F G → Pulls Xo β F F' → Pulls Xo β G G' → Moves Xo b' F' G' := by
  intro E _ _ _ H Dw l Xo S _ x β N k k' _ hk _ b b' hb hb' F G F' G' h hF hG
  subst hk hb
  have := Xo.univ.t.act.hom β
  exact PullMove.isSymAct_of_isNormPull
    ⟨inferInstance, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩ _ _ k N b' hb' h hF hG

end GlobalTheory.PlaceInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace TorsionRat

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_epi {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    letI := i.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (inferInstance : Module.Flat K L)
  have : Surjective (spMap i) := ⟨fun x => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_finset_of_field {K F : Type} [Field K] [Field F] [Algebra K F] {Y : Scheme.{0}} (s : Y ⟶ Sp K)
    [LocallyOfFiniteType s] (p : Sp F ⟶ Y) (hp : p ≫ s = spMap (algebraMap K F)) :
    ∃ S : Finset F, ∀ L : IntermediateField K F, (S : Set F) ⊆ L →
      ∃ q : Sp L ⟶ Y, spMap (algebraMap L F) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(Y, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of K ⟶ Γ(Y, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap K F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : K, f.hom (g.hom r) = algebraMap K F r := fun r => congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra K Γ(Y, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType K Γ(Y, U) from hft).out
  refine ⟨t.image f.hom, fun L hL => ?_⟩
  have hr : ∀ a, f.hom a ∈ L := fun a => by
    have ha : a ∈ Algebra.adjoin K (t : Set Γ(Y, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hL (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ L.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(Y, U) ⟶ CommRingCat.of L := CommRingCat.ofHom (f.hom.codRestrict L hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem exists_finset_over {K F : Type} [Field K] [Field F] [Algebra K F] {X : Scheme.{0}} (G : Over X)
    [LocallyOfFiniteType G.hom] (x : Sp K ⟶ X) (p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G) :
    ∃ S : Finset F, ∀ L : IntermediateField K F, (S : Set F) ⊆ L →
      ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ G, spMap (algebraMap L F) ≫ q.left = p.left := by
  obtain ⟨S, hS⟩ := exists_finset_of_field (pullback.snd G.hom x)
    (pullback.lift p.left (spMap (algebraMap K F)) (Over.w p)) (pullback.lift_snd _ _ _)
  refine ⟨S, fun L hL => ?_⟩
  obtain ⟨q, hq⟩ := hS L hL
  have h1 : spMap (algebraMap L F) ≫ q ≫ pullback.fst G.hom x = p.left := by
    rw [← Category.assoc, hq]; exact pullback.lift_fst _ _ _
  refine ⟨Over.homMk (q ≫ pullback.fst G.hom x) ?_, h1⟩
  haveI := sp_epi (algebraMap L F)
  rw [← cancel_epi (spMap (algebraMap L F))]
  change spMap (algebraMap L F) ≫ (q ≫ pullback.fst G.hom x) ≫ G.hom =
    spMap (algebraMap L F) ≫ spMap (algebraMap K L) ≫ x
  rw [← Category.assoc, h1, ← Category.assoc, sp_comp]
  exact Over.w p

theorem comp_injective {X : Scheme.{0}} {G : Over X} {K L : Type} [Field K] [Field L] {x : Sp K ⟶ X} {y : Sp L ⟶ X}
    (ψ : K →+* L) (g : Over.mk y ⟶ Over.mk x) (hg : g.left = spMap ψ) {a b : Over.mk x ⟶ G}
    (h : g ≫ a = g ≫ b) : a = b := by
  haveI := sp_epi ψ
  have h' : spMap ψ ≫ a.left = spMap ψ ≫ b.left := hg ▸ congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext ((cancel_epi _).1 h')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_level_of_isAlgClosed (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X)
    {M : ℕ} (hM : 0 < M) :
    ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧
      ∀ w : ptO Xo x ⟶ Xo.univ.t.G, w ^ M = 1 ↔ ∃ a, ev a = w := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x β.hom hβ.symm
  exact ⟨I.ev M, I.add M, I.lin M, I.ker M hM, I.onto M hM⟩

theorem exists_enum (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X),
      ∃ u : J → (ptO Xo x ⟶ Xo.univ.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨ev, hadd, -, hker, honto⟩ := exists_level_of_isAlgClosed Xo x hM
  have hI : ∀ a b, ev a = ev b ↔ π a = π b := fun a b => by
    have h : ev a = ev (a - b) * ev b := by rw [← hadd, sub_add_cancel]
    rw [hπ, h, mul_eq_right, hker]
  refine ⟨fun j => ev (r j), fun i j hij => ?_, fun w => (honto w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_eq_comp_of_isAlgClosed (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) {K L : Type} [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] {x : Sp K ⟶ Xo.X} {y : Sp L ⟶ Xo.X} (ψ : K →+* L) (g : ptO Xo y ⟶ ptO Xo x)
    (hg : g.left = spMap ψ) (w : ptO Xo y ⟶ Xo.univ.t.G) (hw : w ^ M = 1) :
    ∃ a : ptO Xo x ⟶ Xo.univ.t.G, a ^ M = 1 ∧ g ≫ a = w := by
  obtain ⟨J, _, hJ⟩ := exists_enum Xo hM
  obtain ⟨u, hu, hu'⟩ := hJ K x
  obtain ⟨v, -, hv'⟩ := hJ L y
  have hp : ∀ j, u j ^ M = 1 := fun j => (hu' _).2 ⟨j, rfl⟩
  choose τ hτ using fun j => (hv' (g ≫ u j)).1 (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  have hτi : Function.Injective τ := fun i j hij =>
    hu (comp_injective ψ g hg (by rw [← hτ, ← hτ, hij]))
  obtain ⟨j, rfl⟩ := (hv' w).1 hw
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hτi j
  exact ⟨u i, hp i, (hτ i).symm⟩

theorem allRat_of_isAlgClosure (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) {L F : Type} [Field L] [Field F] [Algebra L F]
    [IsAlgClosed F] [Algebra.IsAlgebraic L F] (x : Sp L ⟶ Xo.X) (y : Sp F ⟶ Xo.X)
    (hy : spMap (algebraMap L F) ≫ x = y)
    (h : ∀ w : ptO Xo y ⟶ Xo.univ.t.G, w ^ M = 1 →
      ∃ a : ptO Xo x ⟶ Xo.univ.t.G, spMap (algebraMap L F) ≫ a.left = w.left) : AllRat Xo x M := by
  intro Ω _ ψ w hw
  let Ω' := AlgebraicClosure Ω
  let i : Ω →+* Ω' := algebraMap Ω Ω'
  letI : Algebra L Ω' := (i.comp ψ).toAlgebra
  let σ : F →ₐ[L] Ω' := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ : (σ : F →+* Ω').comp (algebraMap L F) = i.comp ψ := σ.comp_algebraMap
  let g₁ : ptO Xo (spMap i ≫ spMap ψ ≫ x) ⟶ ptO Xo (spMap ψ ≫ x) := Over.homMk (spMap i) rfl
  let g₂ : ptO Xo (spMap i ≫ spMap ψ ≫ x) ⟶ ptO Xo y := Over.homMk (spMap (σ : F →+* Ω')) (by
    change spMap (σ : F →+* Ω') ≫ y = spMap i ≫ spMap ψ ≫ x
    rw [← hy, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, hσ])
  obtain ⟨b, hb, hb'⟩ := exists_eq_comp_of_isAlgClosed Xo hM (σ : F →+* Ω') g₂ rfl (g₁ ≫ w)
    (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
  obtain ⟨a, ha⟩ := h b hb
  refine ⟨a, ?_⟩
  haveI := sp_epi i
  have h1 : spMap (σ : F →+* Ω') ≫ b.left = spMap i ≫ w.left := congrArg CommaMorphism.left hb'
  refine (cancel_epi (spMap i)).1 (h1.symm.trans ?_)
  rw [← ha, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, hσ]

theorem exists_finite_allRat (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) {M : ℕ} (hM : 0 < M) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧
      AllRat Xo (spMap (algebraMap K L) ≫ x) M := by
  let F := AlgebraicClosure K
  haveI := Xo.univ.proper
  obtain ⟨J, _, hJ⟩ := exists_enum Xo hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose S hS using fun j => exists_finset_over Xo.univ.t.G x (u j)
  let s : Set F := ⋃ j, (S j : Set F)
  haveI : Finite s := (Set.finite_iUnion fun j => (S j).finite_toSet).to_subtype
  let L := IntermediateField.adjoin K s
  refine ⟨L, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  refine allRat_of_isAlgClosure Xo hM (F := F) _ (spMap (algebraMap K F) ≫ x) ?_ fun w hw => ?_
  · rw [← Category.assoc, sp_comp]
    rfl
  · obtain ⟨j, rfl⟩ := (hu w).1 hw
    exact hS j L ((Set.subset_iUnion (fun j => (S j : Set F)) j).trans (IntermediateField.subset_adjoin _ _))

theorem allRat_baseChange (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {M : ℕ} (h : AllRat Xo x M)
    (L : Type) [Field L] (ψ : K →+* L) : AllRat Xo (spMap ψ ≫ x) M := by
  have key : ∀ (Ω : Type) [Field Ω] (ψ : K →+* Ω) (y : Sp Ω ⟶ Xo.X), y = spMap ψ ≫ x →
      ∀ w : ptO Xo y ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a : ptO Xo x ⟶ Xo.univ.t.G, w.left = spMap ψ ≫ a.left := by
    intro Ω _ ψ y hy
    subst hy
    exact h Ω ψ
  intro Ω _ χ w hw
  obtain ⟨a, ha⟩ := key Ω (χ.comp ψ) _ (by rw [← Category.assoc, sp_comp]) w hw
  let g' : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
  have h1 : (g' ≫ a).left = spMap ψ ≫ a.left := rfl
  refine ⟨g' ≫ a, ha.trans ?_⟩
  exact (congrArg (· ≫ a.left) (sp_comp ψ χ).symm).trans
    ((Category.assoc _ _ _).trans (congrArg (spMap χ ≫ ·) h1.symm))

theorem exists_level_of_allRat (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {M : ℕ} (hM : 0 < M)
    (h : AllRat Xo x M) :
    ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧
      ∀ w : ptO Xo x ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a, ev a = w := by
  let F := AlgebraicClosure K
  let ψ : K →+* F := algebraMap K F
  let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
  have inj : ∀ {a b : ptO Xo x ⟶ Xo.univ.t.G}, g ≫ a = g ≫ b → a = b := fun h => comp_injective ψ g rfl h
  obtain ⟨ev, hadd, hlin, hker, honto⟩ := exists_level_of_isAlgClosed Xo (spMap ψ ≫ x) hM
  choose e he using fun a => h F ψ (ev a) ((honto _).2 ⟨a, rfl⟩)
  have he' : ∀ a, g ≫ e a = ev a := fun a => Over.OverMorphism.ext (he a).symm
  refine ⟨e, fun a b => inj ?_, fun o a => inj ?_, fun a => ?_, fun w hw => ?_⟩
  · rw [MonObj.comp_mul, he', he', he', hadd]
  · rw [← Category.assoc, he', he', hlin]
  · rw [← hker, ← he']
    exact ⟨fun h1 => by rw [h1, MonObj.comp_one], fun h1 => inj (by rw [h1, MonObj.comp_one])⟩
  · obtain ⟨a, ha⟩ := (honto (g ≫ w)).1 (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
    exact ⟨a, inj ((he' a).trans ha)⟩

end TorsionRat


open TorsionRat in
theorem torsion_rational_over_finite_extension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ), 0 < M → (∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ AllRat Xo (spMap (algebraMap K L) ≫ x) M) ∧ (AllRat Xo x M → (∀ (L : Type) [Field L] (ψ : K →+* L), AllRat Xo (spMap ψ ≫ x) M) ∧ ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧ ∀ w : (ptO Xo x ⟶ Xo.univ.t.G), w ^ M = 1 → ∃ a, ev a = w) :=
  fun _ _ _ _ _ _ _ Xo _ _ x _ hM =>
    ⟨exists_finite_allRat Xo x hM, fun h => ⟨fun L _ ψ => allRat_baseChange Xo h L ψ, exists_level_of_allRat Xo hM h⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.PlaceInt

theorem span_mul_prod_of_eq {E T : Type} [Field E] [Fintype T] {F F' : IntermediateField ℚ ℂ} (h : F' = F)
    (A B : Set E) (f : T → E →+* F) (f' : T → E →+* F')
    (hf : ∀ τ x, f' τ x = IntermediateField.equivOfEq h.symm (f τ x)) (m : T → ℕ) (β : F)
    (hβ : Submodule.span (𝓞 F) {β} * ∏ τ, Submodule.span (𝓞 F) (f τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F) (f τ '' B) ^ m τ) :
    Submodule.span (𝓞 F') {IntermediateField.equivOfEq h.symm β} * ∏ τ, Submodule.span (𝓞 F') (f' τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F') (f' τ '' B) ^ m τ := by
  subst h
  have hff : f' = f := funext fun τ => RingHom.ext fun x => hf τ x
  subst hff
  exact hβ

theorem totalDegree_le_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) {k : Type} [Field k] (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : RowDeg r n k a P) :
    P.totalDegree ≤ ∑ τ, ∑ i : Fin (r τ), a τ i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => le_of_eq ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hP m hm σ i

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_embF (τ : E →+* ℂ) (x : E) : d.eF (embF c τ x) = embF d.c₂ τ x := by
  exact Subtype.ext rfl

theorem map_eF_mem_symO (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ symO c Λ) :
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ symO (Dw := Dw) d.c₂ Λ := by
  have key : symO c Λ ≤ (symO (Dw := Dw) d.c₂ Λ).comap (MvPolynomial.map (d.eF : c.F →+* d.c₂.F)) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨⟨d.eF o, ?_⟩, ?_⟩))
      · exact o.2.map (d.eF : c.F →+* d.c₂.F).toIntAlgHom
      · rw [MvPolynomial.map_C]
        rfl
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨σ, i, b, hb, ?_⟩))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [letB, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, RingHom.coe_coe, eF_embF]
  exact key hP

end

theorem eF_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Λ : GenLat E n), (∀ β : c.F, BetaIs (Dw := Dw) c Λ β → BetaIs (Dw := Dw) d.c₂ Λ (d.eF β)) ∧ (∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ Λ w ∧ P.totalDegree ≤ Formalism.L2.Pj.DF Dw w) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E), d.eF (nrm Dw c w α) = nrm Dw d.c₂ w α := by
  intro E _ _ _ H Dw l Xo c n d Λ
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    unfold BetaIs idealAt at hβ ⊢
    exact span_mul_prod_of_eq d.hF (detSet Λ.La) (detSet Λ.Ln) (fun τ => embF c τ) (fun τ => embF d.c₂ τ)
      (fun τ x => (eF_embF d τ x).symm) Dw.mult β hβ
  · intro w P hP
    obtain ⟨hH, hS⟩ := hP
    refine ⟨⟨GlobalTheory.map_mem_HHa Dw.mult n (d.eF : c.F →+* d.c₂.F) d.eF.surjective ComplexEmbedding.conjugate
      (InPsi H) (fun τ i => w (τ, i)) P hH, map_eF_mem_symO d Λ P hS⟩, ?_⟩
    exact totalDegree_le_of_rowDeg Dw.mult n (fun τ i => w (τ, i)) P hH.2.2
  · intro w α
    simp only [nrm, embK, map_prod, map_pow, RingHom.comp_apply, eF_embF]

end GlobalTheory.PlaceInt
end

