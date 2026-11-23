module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianAmpleSymmPreservedFieldBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.FieldBaseChange

theorem inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

theorem abelian_ample_symm_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  intro k Ω _ _ σ A₀ _ hA L hL hamp hsym
  have h := isGrpPullback_pullback A₀ (spMap σ)
  refine ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h, ?_, ?_⟩
  · have := hA.proper
    exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp h.1
  · have hinv := inv_left_comp h
    have i₁ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (pullback.fst A₀.hom (spMap σ))
      (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left _ rfl
    have i₂ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (GrpObj.inv : A₀ ⟶ A₀).left
      (pullback.fst A₀.hom (spMap σ)) _ hinv.symm
    have i₃ := GlobalTheory.RigidBundleGlue.LBIso.pull hsym (pullback.fst A₀.hom (spMap σ))
    exact (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      i₁.symm i₂).trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) i₃

end GlobalTheory.FieldBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfDeRhamUnobstructed
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem NilExp.mono {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {N M : ℕ} (h : NilExp κ N)
    (e : N ≤ M) : NilExp κ M :=
  fun l hl hs ↦ h l hl (e.trans hs)

theorem NilExp.eq_zero {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) {a : R}
    (ha : a ∈ I) : a = 0 := by

  have h1 := h [(1, a)] (by simpa using ha) (by simp)
  simpa [κ.dpow_one ha] using h1

theorem NilExp.eq_sqDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) :
    ∃ hI : I ^ 2 = 0, κ = divided₂ hI := by
  have hbot : I = ⊥ := eq_bot_iff.2 fun a ha ↦ (Ideal.mem_bot).2 (h.eq_zero ha)
  have hI : I ^ 2 = 0 := by
    rw [hbot, pow_two, Ideal.mul_bot]
    rfl
  refine ⟨hI, ?_⟩

  ext n x hx
  obtain rfl := h.eq_zero hx
  rcases n with _ | _ | n
  · rw [κ.dpow_zero hx, (divided₂ hI).dpow_zero hx]
  · rw [κ.dpow_one hx, (divided₂ hI).dpow_one hx]
  · rw [squareZeroDividedPowers_dpow hI (by omega), κ.dpow_eval_zero (by omega)]

theorem abelianLifting_of_sqLifting (hD : AbelianDeRham) (hU : AbelianUnobstructed) (hS : SqLifting) :
    AbelianLifting := by

  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (R₀ : Type) [CommRing R₀]
      (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → NilExp κ (n + 1) →
        LiftObj κ π ∧ LiftHom κ π := by
    intro n
    induction n with
    | zero =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨hI, rfl⟩ := NilExp.eq_sqDP h
      exact hS R I hI R₀ π hπ hker
    | succ n ih =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨R₁, _, J, hJ, ρ, I₁, κ₁, π₁, st, h₁⟩ := exists_isStep_nilExp R R₀ I κ π hπ hker n h
      have hsq := hS R J hJ R₁ ρ st.surj st.kerJ
      have hih := ih R₁ I₁ κ₁ R₀ π₁ st.surj₁ st.ker₁ h₁
      exact ⟨_root_.GlobalTheory.SqLift.liftObj_step hD hU R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.1 hih.1,
        liftHom_of_isStep hD R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.2 hih.2⟩
  intro R _ I κ hκ R₀ _ π hπ hker
  obtain ⟨N, hN⟩ := (isPDNilpotent_iff κ).1 hκ
  exact key N R I κ R₀ π hπ hker (hN.mono (Nat.le_succ N))

theorem abelianLifting_of_schemeLifts :
    AbelianDeRham → AbelianSchemeLifts → AbelianUnobstructed → AbelianLifting := by
  intro hD hL hU
  refine abelianLifting_of_sqLifting hD hU (_root_.GlobalTheory.SqLift.sqLifting_of_noetherian hD ?_)
  intro R _ _ I hI R₀ _ π hπ hk
  exact ⟨_root_.GlobalTheory.SqLift.liftObj_sq hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk),
    _root_.GlobalTheory.SqLift.Hom.liftHom_sq hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk)⟩

end GlobalTheory.SqLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys


open TensorProduct in
theorem oneTmul_surjective_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (M : Type*) [AddCommGroup M] [Module R M] :
    letI := π.toAlgebra
    Function.Surjective (TensorProduct.mk R R₀ M 1) ∧
      ∀ m : M, (1 : R₀) ⊗ₜ[R] m = 0 ↔ m ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ := Ideal.quotientKerAlgEquivOfSurjective (f := (Algebra.ofId R R₀)) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π • (⊤ : Submodule R M)) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)) ≪≫ₗ quotTensorEquivQuotSMul M (RingHom.ker π)
  have hE : ∀ m : M, E (1 ⊗ₜ m) = Submodule.Quotient.mk m := fun m ↦ by
    simp [E, map_one]
  refine ⟨fun t ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (E t)
    exact ⟨m, E.injective (by rw [← hm]; exact hE m)⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← hE, LinearEquiv.map_eq_zero_iff]

theorem mem_smul_top_of_equiv {R : Type} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (L : M ≃ₗ[R] N) (x : M) :
    L x ∈ I • (⊤ : Submodule R N) ↔ x ∈ I • (⊤ : Submodule R M) := by
  have e : (I • ⊤ : Submodule R N) = (I • ⊤ : Submodule R M).map (L : M →ₗ[R] N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 L.surjective]
  rw [e, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem rhoBC_of_abelianLift : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom →
    RhoBC hI hk A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  letI := π.toAlgebra
  have := hA.smooth
  have := hA.proper
  haveI : Smooth A₀.hom := MorphismProperty.of_isPullback (P := @Smooth) h'.1 hA.smooth
  haveI : IsProper A₀.hom := MorphismProperty.of_isPullback (P := @IsProper) h'.1 hA.proper
  have w : i' ≫ A'.hom = A₀.hom ≫ spMap π := h'.1.w
  have hm : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Cris.spMap_id, Category.comp_id]; exact w)
  have hn : IsMor (dp0 R) A'.hom (dp0 R₀) A₀.hom π i' := IsMor.of_dividedPowersZeroIdeal _ w
  have bm : Function.Bijective hm.pull1 :=
    (H1.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
      inferInstance inferInstance inferInstance h'.1 hm).1
  have comp : ∀ c, rho hI hk A₀.hom (hm.pull1 c) = hn.pull1 c := fun c ↦
    IsMor.pullback1_comp hm (redMor hI hk A₀.hom) hn (fun _ ↦ rfl) (Category.id_comp _) c
  have b' := H1.bijective_cechDeRhamComparison_degreeOne A'.hom inferInstance inferInstance inferInstance
  have b₀ := H1.bijective_cechDeRhamComparison_degreeOne A₀.hom inferInstance inferInstance inferInstance
  obtain ⟨⟨e, he⟩, -, -⟩ := (H2 R A' g hA hg).2.2.2.2.2 R₀ A₀.left A₀.hom i' h'.1
  have key : ∀ c, cmp1 A₀.hom (hn.pull1 c) = e (1 ⊗ₜ cmp1 A'.hom c) := fun c ↦
    (pairRes_injective i' A₀.hom).2.2 ((comparison_pullback hn c).symm.trans (he _))
  obtain ⟨hsurj, hker⟩ := oneTmul_surjective_ker I π hπ hk (HH1 A'.hom)
  let L := LinearEquiv.ofBijective hm.pull1 bm
  let C := LinearEquiv.ofBijective (cmp1 A'.hom) b'
  refine ⟨fun y ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨t, ht⟩ := e.surjective (cmp1 A₀.hom y)
    obtain ⟨m, rfl⟩ := hsurj t
    obtain ⟨c', rfl⟩ := b'.2 m
    exact ⟨hm.pull1 c', by rw [comp]; exact b₀.1 ((key c').trans ht)⟩
  · obtain ⟨c', rfl⟩ := bm.2 c
    rw [comp, show hm.pull1 c' = L c' from rfl, mem_smul_top_of_equiv I L c', ← mem_smul_top_of_equiv I C c',
      ← hker]
    change _ ↔ (1 : R₀) ⊗ₜ cmp1 A'.hom c' = 0
    rw [← LinearEquiv.map_eq_zero_iff e, ← key, ← map_zero (cmp1 A₀.hom)]
    exact ⟨fun h ↦ by rw [h], fun h ↦ b₀.1 h⟩

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFrames
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem globalFunctionsConstant_of_constant_after_baseChange (s : X ⟶ Sp R) (hU : UConst s) : CohomZeroIsConstants (OAff s) := by
  refine hU R X s (𝟙 X) ?_
  rw [Algebra.algebraMap_self, Cris.spMap_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {s : X ⟶ Sp R} {n : ℕ} (fr : Frame (OAff s) n) (hc : CohomZeroIsConstants (OAff s))

theorem coboundaryZero_frame_vectorField_globalForm_eq_zero (i : Fin n) (ω : GlobForm s) : d0 (OAff s) (fun T ↦ fr.δ i T (ω.1 T)) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply, ω.2 φ, fr.nat]
  exact sub_self _

def coef (i : Fin n) (ω : GlobForm s) : R := (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose

theorem coef_spec (i : Fin n) (ω : GlobForm s) (T : AffOp X) :
    fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) (coef fr hc i ω) :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose_spec T

theorem coef_eq (i : Fin n) (ω : GlobForm s) (r : R)
    (h : ∀ T, fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) r) : coef fr hc i ω = r :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).unique (coef_spec fr hc i ω) h

def coefL : GlobForm s →ₗ[R] (Fin n → R) where
  toFun ω i := coef fr hc i ω
  map_add' ω ω' := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    rw [coef_spec fr hc i ω T, coef_spec fr hc i ω' T]
  map_smul' r ω := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply,
      smul_eq_mul, map_mul, Algebra.smul_def]
    rw [coef_spec fr hc i ω T]

def sumL : (Fin n → R) →ₗ[R] GlobForm s where
  toFun c := ∑ i, c i • fr.w i
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, mul_smul]

theorem sumL_coefL (ω : GlobForm s) : sumL fr (coefL fr hc ω) = ω := by
  apply Subtype.ext
  funext T
  conv_rhs => rw [fr.sum T (ω.1 T)]
  simp only [sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coef_spec, algebraMap_smul]


include fr hc in
theorem projective : Module.Projective R (GlobForm s) :=
  Module.Projective.of_split (coefL fr hc) (sumL fr) (LinearMap.ext (sumL_coefL fr hc))

def back (U : AffOp X) (x : Ω[Sec s U.unop.1⁄R]) : Sec s U.unop.1 ⊗[R] GlobForm s :=
  ∑ i, (fr.δ i U x : Sec s U.unop.1) ⊗ₜ[R] fr.w i

theorem back_add (U : AffOp X) (x y : Ω[Sec s U.unop.1⁄R]) : back fr U (x + y) = back fr U x + back fr U y := by
  simp only [back, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]


include fr hc in
theorem par (U : AffOp X) : IsBaseChange (Sec s U.unop.1) (evForm s U) := by
  change Function.Bijective (TensorProduct.lift _)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨back fr U, fun t ↦ ?_, fun x ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp [back]
    | tmul a ω =>
      simp only [TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
      conv_rhs => rw [← sumL_coefL fr hc ω]
      simp only [back, sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← TensorProduct.smul_tmul]
      congr 1
      change fr.δ i U (a • ω.1 U) = coef fr hc i ω • a
      rw [(fr.δ i U).map_smul a (ω.1 U), coef_spec fr hc i ω U, Algebra.smul_def, mul_comm]
      rfl
    | add t t' ht ht' => rw [map_add (f := _), back_add, ht, ht']
  · conv_rhs => rw [fr.sum U x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [back, map_sum, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
    rfl

end GlobalTheory.FormsOnAb

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

theorem formSt_of (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
      GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) : FormSt := by
  intro R₀ _ A _ g hA hs
  obtain ⟨⟨n, ⟨fr⟩⟩, hU, hP⟩ := H R₀ A g hA hs
  have hc := globalFunctionsConstant_of_constant_after_baseChange A.hom hU
  refine ⟨fun U ↦ par fr hc U, projective fr hc, fun w wm w₁ w₂ hm h1 h2 ↦ ?_⟩
  rw [hm.eq_pullForm, h1.eq_pullForm, h2.eq_pullForm]
  exact hP w

end GlobalTheory.FormsOnAb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIsoAny

open GlobalTheory.NearFibreIso GlobalTheory.DenseFibreIso

theorem exists_away_bijective_of_fg {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (R K : Type) [CommRing R] [CommRing K]
    [Algebra R K] [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B]
    (hs : Function.Surjective (algebraMap A B))
    (hfg : (RingHom.ker (algebraMap A B)).FG)
    (h : Function.Injective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    (m : PrimeSpectrum (A ⊗[R] K)) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧ Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  let I : Submodule A A := LinearMap.ker (Algebra.linearMap A B)
  have : Module.Finite A I := Module.Finite.iff_fg.2 hfg
  have hex : Function.Exact I.subtype (Algebra.linearMap A B) := LinearMap.exact_subtype_ker_map _
  have hinj : Function.Injective ((I.subtype.restrictScalars R).rTensor K) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj K _).1
      (LinearMap.lTensor_injective_of_exact_of_flat ((Algebra.linearMap A B).restrictScalars R) hs
        (I.subtype.restrictScalars R) Subtype.val_injective hex K)
  have h1 : Subsingleton (I ⊗[R] K) := by
    refine subsingleton_of_forall_eq 0 fun z => hinj (h ?_)
    rw [map_zero, map_zero]
    induction z with
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
    | tmul x c =>
      have e : (x : A) ⊗ₜ[R] c = (x : A) • ((1 : A) ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      have hx : (x : A) • (1 : B) = 0 := by
        rw [← Algebra.algebraMap_eq_smul_one]; exact x.2
      change ((x : A) ⊗ₜ[R] c) ⊗ₜ[A] (1 : B) = 0
      rw [e, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]
  have h2 : Subsingleton ((A ⊗[R] K) ⊗[A] I) :=
    ((TensorProduct.comm A _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I K)).toEquiv.subsingleton
  obtain ⟨a, ha, ha'⟩ := exists_smul_eq_zero (A := A) (N := I) (A ⊗[R] K) m
  refine ⟨a, ha, ?_⟩
  have h3 := subsingleton_of_isUnit ha' (Localization.Away a)
    (IsLocalization.Away.algebraMap_isUnit a)
  rw [includeLeft_eq, EquivLike.bijective_comp]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, LinearMap.lTensor_surjective _ hs⟩
  obtain ⟨y, rfl⟩ := (lTensor_exact (Localization.Away a) hex hs z).1 hz
  rw [Subsingleton.elim y 0, map_zero]


set_option backward.isDefEq.respectTransparency.types false in
theorem near_isIso_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [hcl : IsClosedImmersion f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x hx
  have h1 : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap (algebraMap A B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H ‹_›
  have e : spMap (algebraMap R B) = j' ≫ f ≫ s := by
    rw [← H.w_assoc, hj, ← Spec.map_comp, IsScalarTower.algebraMap_eq R A B]; rfl
  have h2 : Flat (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h2)
  have h3 : LocallyOfFinitePresentation (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have h4 : LocallyOfFinitePresentation (spMap (algebraMap R A)) := by
    rw [← hj]; infer_instance
  have : Algebra.FinitePresentation R B := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h3)
  have : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h4)
  have hfg : (RingHom.ker (algebraMap A B)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom R A B) hs
  obtain ⟨a, ha, ha'⟩ := exists_away_bijective_of_fg R K hs hfg hb.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.2 ha'⟩

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : Smooth s := h₁.smooth
    have : Smooth (f' ≫ s) := h₂.smooth
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := GlobalTheory.AbMonoIso.fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_finitePresentation s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S B B' _ _ hB hB' g hg hg' x _ _
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIsoAny
end
end

