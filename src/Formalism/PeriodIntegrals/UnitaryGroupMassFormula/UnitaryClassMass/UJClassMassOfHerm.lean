module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PPatchF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0002

@[expose] public section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem surjStep_of_herm' (hH : HermApprox) : SurjStep := surjStep_of_herm hH lsOne

theorem uJClassMass_of_herm (hH : HermApprox) : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_open lattice_modification (surjStep_of_herm' hH)

end PI.UnitaryGroupMassFormula.UJClassMass
