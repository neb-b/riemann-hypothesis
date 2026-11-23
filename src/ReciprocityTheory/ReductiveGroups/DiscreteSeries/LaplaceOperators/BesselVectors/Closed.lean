module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.BesselNVGOfNv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Imports
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.FamilyGapImplicationHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Bundle0001

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed

theorem nvAll : NVStatement := nv NVHTop.intS

theorem besselNVG : TopNV.BesselNVG := TopFinal.besselNVG_of_nv nvAll

end ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed
