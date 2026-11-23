module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.AlgebraMapMemRange

@[expose] public section

namespace PI.LocalEndW

theorem localEndHomeo_of_three (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt) :
    PI.LocalEndHomeo :=
  localEndHomeo_of hA hB1 hB2 valContinuous valSurjective

end PI.LocalEndW
