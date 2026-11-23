module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.CardNonzero

@[expose] public section

namespace PI.GGMirBoundW

theorem mirabolicBound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  mirabolicBound_of_steps baseProp stepOf blkFacts colFacts conjCol rowExists charOrth sepLemma

end PI.GGMirBoundW
