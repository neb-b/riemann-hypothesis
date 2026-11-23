module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.BesselNV
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ParitySignEqGapSign
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0016

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

theorem bAtTarget_of (hNV : NVStatement) : BAtTargetStatement := by
  intro k r z c u v b h hS
  obtain ⟨hk, -, -, -, -, -, hHC, hI, hH, hL, hG⟩ := hS
  exact hNV k r u v b h hk hHC hI hH hL hG

theorem besselNVG_of_nv (hNV : NVStatement) : TopNV.BesselNVG :=
  TopNV.besselNVG_of (bAtTarget_of hNV) (sigZero fun m => S7.psiAll (n := m))

end ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal
