module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0003

@[expose] public section

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsTotPosDef (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ x : V, x ≠ 0 → ∀ φ : K →+* ℂ, 0 < (φ (h x x)).re

end Defs

def conjO (K : Type*) [Field K] [StarRing K] : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (starRingEnd K)

end ReciprocityTheory.ChartRestriction.L3
