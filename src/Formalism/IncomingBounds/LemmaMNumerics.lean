module

public import Formalism.IncomingBounds.Bundle0001

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

def FactValBounds : Prop :=
  ∀ l : ℕ, l.Prime → ∀ N : ℕ, 1 ≤ N →
    (N : ℝ) / ((l : ℝ) - 1) - (Real.logb l N + 1) ≤ (padicValNat l N.factorial : ℝ) ∧
      (padicValNat l N.factorial : ℝ) ≤ ((N : ℝ) - 1) / ((l : ℝ) - 1)

end Formalism.IncomingBounds
