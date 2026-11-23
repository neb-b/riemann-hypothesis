module

public import Mathlib

@[expose] public section

noncomputable section

namespace SiegelEisensteinSeries

open Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def WHolo (D : Set (E →ₗ[ℂ] ℂ)) (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ ν ∈ D, DifferentiableOn ℂ (fun s => ν (f s)) U

variable {I : Type*}

end SiegelEisensteinSeries
