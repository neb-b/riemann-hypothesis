module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Num

variable {ε : Fin n → Bool}

theorem gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : 2 * (n : ℝ) < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by
  have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  constructor <;> linarith

end Num

end ReciprocityTheory.ChartRestriction.DS.G2
