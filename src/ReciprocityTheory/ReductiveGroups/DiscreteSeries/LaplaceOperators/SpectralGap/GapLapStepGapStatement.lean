module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def GapLapStepGapStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), 1 ≤ pOf ε → 1 ≤ qOf ε → GapLap ε lam h →
    StepGap ε (qOf ε - 1) h

end ReciprocityTheory.ChartRestriction.DS.Lap
