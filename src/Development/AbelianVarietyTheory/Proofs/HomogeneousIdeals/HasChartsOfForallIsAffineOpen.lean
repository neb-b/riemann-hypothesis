module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp)

namespace GlobalTheory.NatFun

variable {k : Type} [CommRing k]

section Points

scoped instance sectionsAlgebra (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    Algebra k Γ(X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom.toAlgebra

theorem algebraMap_sections (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    algebraMap k Γ(X.left, U) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom := rfl

variable {X : Over (Spec (CommRingCat.of k))}
variable {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

theorem spMap_injective : Function.Injective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro φ ψ h
  have h1 : (spMap φ).left = (spMap ψ).left := by rw [h]
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))

theorem spMap_surjective : Function.Surjective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro m
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of B) m.left
  have h : CommRingCat.ofHom (algebraMap k A) ≫ φ = CommRingCat.ofHom (algebraMap k B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w m
  exact ⟨⟨φ.hom, fun c => congr(($h).hom c)⟩, Over.OverMorphism.ext hφ⟩

def affinePoint {U : X.left.Opens} (hU : IsAffineOpen U) : sp Γ(X.left, U) ⟶ X :=
  Over.homMk hU.fromSpec (by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    change hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, U)))
    rw [← h, algebraMap_sections, CommRingCat.ofHom_hom, Spec.map_comp])

end Points

section Families

abbrev AlgClass (k : Type) [CommRing k] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra k A], Prop

variable {𝒯 𝒯' : AlgClass k} {X : Over (Spec (CommRingCat.of k))}



section
variable (A : Type) [CommRing A] [Algebra k A] (hA : 𝒯 A) (x : sp A ⟶ X)

end




end Families

end GlobalTheory.NatFun
