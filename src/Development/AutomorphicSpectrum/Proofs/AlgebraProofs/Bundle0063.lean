module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureFamilyDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem pure_family_spans_pure_sublattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (n : ℕ), IsPure hP x → (∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x)) → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) ∧ (∀ y ∈ PureType.lat hP (sgnRt H true), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))) ∧ ∀ y ∈ PureType.lat hP (sgnRt H false), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) :=
  @PositivityTheory.Xgf.pure_family_decomposition

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureTypeLatticesOrthogonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PureOrth

theorem sesq_eq_zero_of_opposite_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (a b : D.La), a ∈ PureType.lat hP (sgnRt H true) → b ∈ PureType.lat hP (sgnRt H false) → sesq D a b = 0 ∧ sesq D b a = 0 :=
  @PositivityTheory.Xgf.pure_type_lattices_orthogonal

end GlobalTheory.CompanionTheory.Ar.PureOrth
end

