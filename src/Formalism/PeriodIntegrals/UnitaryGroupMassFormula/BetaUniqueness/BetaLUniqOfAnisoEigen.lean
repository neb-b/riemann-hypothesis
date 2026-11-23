module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.AgreeOnH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.LineReduce
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.WAniso

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.BetaLUniq

theorem betaLUniq_of_aniso_eigen (h3 : WAniso) (h5 : EigenvalueLastLineOne) : PI.BetaLUniq :=
  betaLUniq_of'' gram_matrix_nondegenerate agreeOnH h3 h5

end PI.UnitaryGroupMassFormula.BetaLUniq
