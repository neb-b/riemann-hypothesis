module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.GenEqOf

@[expose] public section

namespace PI.SSE

theorem sigmaStarEx : PI.SigmaStarEx :=
  sigmaStarEx_of_parts thetaA thetaDerivNe reduceBasis genEqOf latExt

end PI.SSE
