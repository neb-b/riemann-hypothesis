module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem isIso_of_isIso_left {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIso f.hom.left] : IsIso f := by
  have : IsIso ((Over.forget _).map f.hom) := by simpa using (inferInstance : IsIso f.hom.left)
  have : IsIso f.hom := isIso_of_reflects_iso f.hom (Over.forget _)
  have : IsMonHom (inv f.hom) := inferInstanceAs (IsMonHom (asIso f.hom).inv)
  let g : B ⟶ A := Hom.mk (A := B) (B := A) (inv f.hom)
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    change Hom.hom (f ≫ g) = Hom.hom (𝟙 A)
    simp [g]
  · apply Subtype.ext
    change Hom.hom (g ≫ f) = Hom.hom (𝟙 B)
    simp [g]

instance isIso_left_of_isIso {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIso f] : IsIso f.hom.left := by
  have : IsIso f.hom := ⟨(inv f).hom, by rw [← comp_hom, IsIso.hom_inv_id, id_hom], by rw [← comp_hom, IsIso.inv_hom_id, id_hom]⟩
  exact (inferInstance : IsIso ((Over.forget _).map f.hom))

theorem isIso_iff_deg_eq_one : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    (IsIso f → IsIsogeny f ∧ deg f = 1) ∧ (deg f = 1 → IsIso f) := by
  intro K _ A B f
  refine ⟨fun hf => ?_, fun hd => ?_⟩
  · have hI : IsIsogeny f := ⟨inferInstance, inferInstance⟩
    refine ⟨hI, ?_⟩
    rw [deg, if_pos hI, Scheme.Hom.finrank_eq_one_of_isIso]
    rfl
  · have hI : IsIsogeny f := by
      by_contra h
      rw [deg, if_neg h] at hd
      exact zero_ne_one hd
    obtain ⟨-, hfl, -, hr⟩ := _root_.GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B f hI
    have : IsFinite f.hom.left := hI.1
    have : IsIso f.hom.left := by
      rw [Scheme.Hom.isIso_iff_finrank_eq]
      funext y
      rw [hr y, hd]
      rfl
    exact isIso_of_isIso_left f

end GlobalTheory.AV.AbVar
