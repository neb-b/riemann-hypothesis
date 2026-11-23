module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0011

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem k2Vd (n : ℕ) : EigenspaceWeightConeDual n :=
  TwistedDualLemmas.dualLowestKType_of_standard (k2V n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
