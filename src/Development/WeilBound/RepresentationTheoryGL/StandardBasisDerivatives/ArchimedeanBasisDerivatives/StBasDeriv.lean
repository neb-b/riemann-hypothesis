module

public import Mathlib

@[expose] public section

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace PositivityTheory.Rg.Pc1

variable {n : ℕ}

def IsProfile (N : ℕ) (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ (∀ x, 1 ≤ x → G x = 0) ∧ (∀ x, 0 ≤ (-1) ^ N * iteratedDeriv N G x) ∧ iteratedDeriv N G 0 ≠ 0

end PositivityTheory.Rg.Pc1
