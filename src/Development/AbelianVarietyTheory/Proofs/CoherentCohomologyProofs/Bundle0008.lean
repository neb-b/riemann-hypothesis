module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanMatrix

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.QCoh.Qcqs

section Base

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

def baseRingHom (p : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U le_top

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_res (p : X ⟶ Spec R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseRingHom p U r) = baseRingHom p V r := by
  rw [← ConcreteCategory.comp_apply, baseRingHom, Category.assoc, Scheme.Hom.appLE_map]
  rfl

theorem baseRingHom_top (p : X ⟶ Spec R) :
    baseRingHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by
  rw [baseRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_app (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) :
    baseRingHom p U ≫ g.app U = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) := by
  rw [baseRingHom, baseRingHom, Category.assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]

theorem app_baseRingHom (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) (r : R) :
    g.app U (baseRingHom p U r) = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) r := by
  rw [← baseRingHom_comp_app]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_SpecMap {L : CommRingCat.{u}} (q : Y ⟶ Spec L) (ι : R ⟶ L)
    (V : Y.Opens) : baseRingHom (q ≫ Spec.map ι) V = ι ≫ baseRingHom q V := by
  rw [baseRingHom, baseRingHom, Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  exact congrArg _ (Scheme.Hom.appLE_comp_appLE q (Spec.map ι) ⊤ ⊤ V le_top le_top).symm

end Base

section Localization

variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))

include H

omit S in
theorem baseRingHom_algebraMap (V : Y.Opens) (r : R) :
    baseRingHom q V (algebraMap R L r) = baseRingHom (g ≫ p) V r := by
  rw [H.w, baseRingHom_comp_SpecMap]; rfl


theorem isLocalization_app {V : X.Opens} (hV : IsAffineOpen V) :
    @IsLocalization Γ(X, V) _ (S.map (baseRingHom p V).hom) Γ(Y, g ⁻¹ᵁ V) _
      (g.app V).hom.toAlgebra := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have po' : IsPushout (baseRingHom p V) (CommRingCat.ofHom (algebraMap R L)) (g.app V)
      (baseRingHom q (g ⁻¹ᵁ V)) := by
    refine po.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso L) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [baseRingHom]
  let := (g.app V).hom.toAlgebra
  let := (baseRingHom p V).hom.toAlgebra
  let := (baseRingHom q (g ⁻¹ᵁ V)).hom.toAlgebra
  let := (baseRingHom (g ≫ p) (g ⁻¹ᵁ V)).hom.toAlgebra
  have : IsScalarTower R Γ(X, V) Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (app_baseRingHom g p V r).symm
  have : IsScalarTower R L Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap H _ r).symm
  exact (Algebra.isLocalization_iff_isPushout S L).mpr
    (CommRingCat.isPushout_iff_isPushout.mp po')

end Localization

end GlobalTheory.QCoh.Qcqs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
section
open Module IsDiscreteValuationRing

namespace GlobalTheory

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section Cokernel

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  first
  | (rename_i h_1 h_2 h_3; revert R h_1 h_2 h_3 ι s a; exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod)
  | exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | (apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod ..)

theorem length_quotient_range_eq_top_of_det_eq_zero [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (hf : LinearMap.det f = 0) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 f hf; exact @_root_.GlobalTheory.LengthDualFunctional.main)
  | exact @_root_.GlobalTheory.LengthDualFunctional.main
  | exact _root_.GlobalTheory.LengthDualFunctional.main
  | (apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthDualFunctional.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthDualFunctional.main ..)

theorem length_quotient_eq_addVal_det_equiv [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) = addVal R (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 N e; exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det)
  | exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det ..)

theorem length_quotient_range_eq_addVal_det [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.det f = 0
  · rw [length_quotient_range_eq_top_of_det_eq_zero hf, hf, addVal_zero]
  · have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      by_contra h
      exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
    exact length_quotient_eq_addVal_det_equiv _ (LinearEquiv.ofInjective f hinj)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem length_quotient_range_toLin'_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range (Matrix.toLin' P)) = addVal R P.det := by
  rw [length_quotient_range_eq_addVal_det, LinearMap.det_toLin']

theorem length_quotient_range_mulVecLin_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det :=
  length_quotient_range_toLin'_eq_addVal_det P

theorem length_quotient_range_eq_addVal_det_toMatrix {M' : Type*} [AddCommGroup M'] [Module R M']
    (b' : Basis ι R M') (b : Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.toMatrix b' b f).det := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9 h_11 h_12; revert R h_1 h_2 h_3 M h_5 h_6 ι h_8 h_9 M' h_11 h_12 b' b f; exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main)
  | exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main
  | exact _root_.GlobalTheory.LengthQuotientSpanValuation.main
  | (apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientSpanValuation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientSpanValuation.main ..)

theorem length_quotient_span_eq_addVal_det (b : Basis ι R M) (v : ι → M) :
    Module.length R (M ⧸ Submodule.span R (Set.range v)) = addVal R (b.det v) := by
  rw [← b.constr_range R, length_quotient_range_eq_addVal_det_toMatrix b b, Basis.det_apply,
    Basis.toMatrix_eq_toMatrix_constr]
  rfl

end Cokernel

section Relative

variable {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Relative

section Lattice

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem ordFrac_algebraMap_eq_exp {x : R} {n : ℕ} (h : addVal R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  rw [Ring.ordFrac_eq_ord R, Ring.ordMonoidWithZeroHom_eq_coe R
    (mem_nonZeroDivisors_of_ne_zero hx) ((Ring.ord_eq_addVal x).trans h)]
  rfl

theorem ordFrac_unit_mul_zpow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ) :
    Ring.ordFrac R (algebraMap R K u * algebraMap R K ϖ ^ n) = WithZero.exp n := by
  rw [map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible hϖ, one_mul,
    ← WithZero.exp_zsmul, smul_eq_mul, mul_one]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signedLength_span_eq_of_det_eq_unit_mul_zpow {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ)
    (n : ℤ) (hg : g.det = algebraMap R K u * algebraMap R K ϖ ^ n) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) = n := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14 h_15; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 ι h_14 h_15 a b ha g hb ϖ hϖ u n hg; exact @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq)
  | exact @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq
  | exact _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq
  | (apply _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq ..)

omit [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R] [Fintype ι] [DecidableEq ι] in
private theorem span_range_coe_basis {A : Submodule R V} (a : Basis ι R A) :
    Submodule.span R (Set.range fun i => (a i : V)) = A := by
  conv_rhs => rw [← Submodule.map_subtype_top A, ← a.span_eq, Submodule.map_span,
    ← Set.range_comp]
  rfl

end Lattice

end GlobalTheory
end

