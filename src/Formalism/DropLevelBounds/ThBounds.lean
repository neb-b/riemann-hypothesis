module

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.UnitaryBoundIntegral

def thl (k l : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ i : ℕ, Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i ∧ t = ((l : ℝ) ^ i)⁻¹}

def ThBounds : Prop :=
  ∀ (k l : ℕ), 1 ≤ k → 2 ≤ l →
    thl k l ≤ ((l : ℝ) ^ 3)⁻¹ ∧ thl k l < ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹ ∧
      ((k : ℝ) < (l : ℝ) ^ 2 → thl k l = ((l : ℝ) ^ 3)⁻¹)

end Formalism.UnitaryBoundIntegral
