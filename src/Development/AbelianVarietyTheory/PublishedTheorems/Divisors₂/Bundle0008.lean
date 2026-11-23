module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianLifting : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
      GrothendieckMessing.LiftObj κ π ∧ GrothendieckMessing.LiftHom κ π

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianUnobstructed : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Published

def GrothendieckDeformation : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
      GrothendieckMessing.At κ π

namespace GrothendieckDeformation


set_option autoImplicit false in
open DividedPowers in
theorem _root_.GlobalTheory.Published.GrothendieckDeformation.grothendieckMessing (H : _root_.GlobalTheory.Published.GrothendieckDeformation) :
    _root_.GlobalTheory.Published.GrothendieckMessing := by
  unfold _root_.GlobalTheory.Published.GrothendieckMessing
  intro _ _ R _ _ I κ hκ R₀ _ π hπ hker
  exact H R I κ hκ R₀ π hπ hker


set_option autoImplicit false in
open DividedPowers in
theorem _root_.GlobalTheory.Published.GrothendieckDeformation.at_dualNumber (H : _root_.GlobalTheory.Published.GrothendieckDeformation) (R : Type)
    [CommRing R] :
    _root_.GlobalTheory.Published.GrothendieckMessing.At
      (_root_.GlobalTheory.DeRham.epsDP R) (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine H _ _ (_root_.GlobalTheory.DeRham.epsDP R) ?_ R _ (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
    rfl
  unfold _root_.GlobalTheory.DeRham.epsDP
  exact _root_.GlobalTheory.Cris.isDPNilpotent_squareZero _

end GrothendieckDeformation

end GlobalTheory.Published
end
end

