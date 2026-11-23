module

public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
open scoped TensorProduct
namespace PI.GreenHCLabel

def SimpleIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrrRep τ.ρ

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

variable {K}

end PI.GreenHCLabel
