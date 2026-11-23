module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.CongruenceLiftOfBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0007

@[expose] public section

namespace PI.LocMassTypL

open PI.LocMassTypW

theorem index_formula_of_split (hS : SplitR) (hU : KUnip1) : StepIdx :=
  index_formula_of_lift (congruence_lift_of_split hS) hU

end PI.LocMassTypL
