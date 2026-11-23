module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRhamCpl

open GlobalTheory.PDiv (ModPow)

section Rings

variable (p : ℕ) (O : Type) [CommRing O]

end Rings

section BaseChange

variable {O O' B B' : Type} [CommRing O] [CommRing O'] [CommRing B] [CommRing B']

abbrev bcObj (a : O →+* B) (A : Over (Sp O)) : Over (Sp B) := (Over.pullback (spMap a)).obj A

instance bcObj.instGrpObj (a : O →+* B) (A : Over (Sp O)) [GrpObj A] : GrpObj (bcObj a A) :=
  Functor.grpObjObj

end BaseChange

section Levels

variable (p : ℕ) {O : Type} [CommRing O]

variable {p} {A : Over (Sp O)} [GrpObj A]


end Levels

abbrev Family (p : ℕ) : Type 1 :=
  ∀ ⦃R : Type⦄ [CommRing R], IsAdicComplete (Ideal.span {(p : R)}) R →
    ∀ ⦃A : Over (Sp R)⦄ [GrpObj A],
      IsAbelianScheme A → (∃ g : ℕ, SmoothOfRelativeDimension g A.hom) →
      ∀ ⦃G : PDivGroup p R⦄, G.TorsionTower A → (primDR A ≃ₗ[R] G.RigExt)

variable {p : ℕ} (E : Family p)

end GlobalTheory.DeRhamCpl
