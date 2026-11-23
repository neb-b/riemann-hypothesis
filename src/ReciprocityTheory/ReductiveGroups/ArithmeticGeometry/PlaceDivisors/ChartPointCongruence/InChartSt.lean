module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0002

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

attribute [local instance] Over.cartesianMonoidalCategory

def SepSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsHausdorff (Ideal.span {p}) O → ∀ h h' : A →ₐ[T] O,
      (∀ n : ℕ, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = (Ideal.Quotient.mkₐ T _).comp h') → h = h'

def AlgLimSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsAdicComplete (Ideal.span {p}) O → ∀ a : ∀ n : ℕ, A →ₐ[T] O ⧸ Ideal.span {p ^ n},
      (∀ (n : ℕ) (z : A) (y : O), Ideal.Quotient.mk _ y = a (n + 1) z → Ideal.Quotient.mk _ y = a n z) →
      ∃ h : A →ₐ[T] O, ∀ n, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = a n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
