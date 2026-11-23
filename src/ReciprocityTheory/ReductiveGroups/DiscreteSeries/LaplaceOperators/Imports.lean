module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ParitySignEqGapSign
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.StepIBase
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ImportsAlt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem nv (hIS : S0.IntSStatement) : NVStatement :=
  nv_of Base.stepIBase step hIS S0.DecDeriv.decDeriv

end ReciprocityTheory.ChartRestriction.DS.Lap
