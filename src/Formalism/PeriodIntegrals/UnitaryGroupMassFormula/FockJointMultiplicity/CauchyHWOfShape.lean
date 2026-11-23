module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0006

@[expose] public section

namespace PI.FJMB

theorem cauchyHW_of_shape (hS : HypShape) : PI.FJM.CauchyHW :=
  cauchy_highest_weight_of_shape hS diagonal_hypothesis diagonal_image_block_free

end PI.FJMB
