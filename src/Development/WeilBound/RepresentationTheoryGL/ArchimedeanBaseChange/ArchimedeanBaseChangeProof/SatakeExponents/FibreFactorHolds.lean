module

public import Mathlib

@[expose] public section

noncomputable section

open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def ExpSum : Prop := ∀ (ι : Type) [Fintype ι] (c lam : ι → ℂ) (ρ C : ℝ) (N : ℕ), 0 ≤ ρ →
  (∀ᶠ k : ℕ in Filter.atTop, ‖∑ i, c i * lam i ^ k‖ ≤ C * (1 + k) ^ N * ρ ^ k) →
  ∀ μ : ℂ, ρ < ‖μ‖ → ∑ i with lam i = μ, c i = 0

end PositivityTheory.Rg.BcB.F

end
