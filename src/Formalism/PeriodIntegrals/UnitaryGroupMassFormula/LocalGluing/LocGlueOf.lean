module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.Bundle0001

@[expose] public section

namespace PI.LocHerm.Glue

theorem locGlue_of (hO : PI.LocHerm.LocOProj) : PI.LocHerm.LocGlue :=
  locGlue_of_pair (pair_of rieszRepresentation_holds existsIntegralMultiple hO)

end PI.LocHerm.Glue
