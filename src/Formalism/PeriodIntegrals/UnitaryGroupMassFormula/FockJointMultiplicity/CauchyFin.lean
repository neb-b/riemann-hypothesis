module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHWOfShape
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0006

@[expose] public section

namespace PI.FJM

theorem cauchy_highest_weight : CauchyHW :=
  PI.FJMB.cauchyHW_of_shape PI.FJMX.minorProductDiagonal

end PI.FJM
