module

public import Mathlib

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.ConjugateSelfDual

abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def IsPlaceOver (A : ValuationSubring (Ω)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F (Ω) (x : F)) < 1 ↔ x ∈ v.asIdeal

def Inertia (A : ValuationSubring (Ω)) : Set (G F Ω) :=
  {σ | σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}

end Formalism.ConjugateSelfDual
