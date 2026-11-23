module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Partial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPow

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

theorem indexEq_of_traceInt (h : TraceInt) : PI.AdIndexEq.IndexEq :=
  indexEq_of_open gl_character (qReflPow_of h)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
