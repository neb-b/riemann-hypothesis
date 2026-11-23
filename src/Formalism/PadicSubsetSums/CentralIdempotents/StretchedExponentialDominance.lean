module

public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots

@[expose] public section

open Finset

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

def StretchedExponentialDominance : Prop :=
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
    x ^ C * Real.exp (-x ^ (ε / 6)) ≤ 1 / 20 * Real.exp (-x ^ (ε / 7))

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
