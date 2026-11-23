module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.Bundle0001

@[expose] public section

namespace PI.SSU

theorem sigmaStarUniq_of (h : AreaLat) : SigmaStarUniq :=
  main_of (key_of siegel_set_shift_invariance siegel_set_completeness) h

end PI.SSU
