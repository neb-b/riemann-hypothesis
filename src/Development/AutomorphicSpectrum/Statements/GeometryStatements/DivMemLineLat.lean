module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptInputs

theorem labelEmb_inr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : CMType H) : labelEmb c (.inr τ) = tauIn c (ComplexEmbedding.conjugate τ.1) := by
  ext a
  show τ.1 ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ.1 (a : E)
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj (K := E) τ.1 (a : E)

theorem labelEmb_inl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : CMType H) : labelEmb c (.inl τ) = tauIn c τ.1 := rfl

end GlobalTheory.CompanionTheory.Ar.Flat.CptInputs
