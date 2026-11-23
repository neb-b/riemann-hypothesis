module

public import Mathlib

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.SectionsCommRing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def structureHom (s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom

theorem map_structureHom (s : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (structureHom s U r) = structureHom s V r := by
  show ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = _
  rw [← X.presheaf.map_comp]
  rfl

def Sections (_s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : Type u := Γ(X, U)

namespace Sections

variable (s : X ⟶ Spec (CommRingCat.of R))

instance (U : X.Opens) : CommRing (Sections s U) := inferInstanceAs (CommRing Γ(X, U))

instance (U : X.Opens) : Algebra R (Sections s U) :=
  RingHom.toAlgebra (R := R) (S := Sections s U) (structureHom s U)

def restrict {U V : X.Opens} (h : V ≤ U) : Sections s U →ₐ[R] Sections s V where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' r := map_structureHom s h r

end Sections

end GlobalTheory.SectionsCommRing
