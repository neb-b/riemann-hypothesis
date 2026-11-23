module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CoverDenseAlt

variable {Z : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A']

def val (z : Sp A ⟶ Z) (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) : Γ(Z, V) →+* A :=
  (z.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem val_comp (φ : A →+* A') (z : Sp A ⟶ Z) (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) {z' : Sp A' ⟶ Z}
    (e : z' = spMap φ ≫ z) (h' : ⊤ ≤ z' ⁻¹ᵁ V) (s : Γ(Z, V)) :
    val z' V h' s = φ (val z V h s) := by
  subst e
  have h1 : (spMap φ ≫ z).appLE V ⊤ h' = z.appLE V ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : (spMap φ ≫ z).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom =
      z.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [h1, Category.assoc, Scheme.ΓSpecIso_naturality]
  unfold val
  rw [h2]
  rfl

theorem val_rep (z : Sp A ⟶ Z) {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U) :
    spMap (val z U h) ≫ hU.fromSpec = z := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec z hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  change Spec.map (z.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ hU.fromSpec = z
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem val_ext {z z' : Sp A ⟶ Z} {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : ∀ s, val z U h s = val z' U h' s) : z = z' := by
  rw [← val_rep z hU h, ← val_rep z' hU h', RingHom.ext e]

theorem exists_affine {B : Type} [CommRing B] [IsLocalRing B] (z : Sp B ⟶ Z) :
    ∃ U : Z.Opens, IsAffineOpen U ∧ ⊤ ≤ z ⁻¹ᵁ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (z (IsLocalRing.closedPoint B))) isOpen_univ
  exact ⟨U, hU, (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of B) z hxU).ge⟩

theorem spMap_spMap {A'' : Type} [CommRing A''] (φ : A →+* A') (ψ : A' →+* A'') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

variable (J : Ideal A)

end CoverDenseAlt
