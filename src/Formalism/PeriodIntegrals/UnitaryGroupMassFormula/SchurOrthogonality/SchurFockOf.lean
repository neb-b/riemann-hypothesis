module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionC

@[expose] public section

noncomputable section

namespace PI.WSF

theorem schurFock_of (h : PI.HwIrred) : PI.SchurFock :=
  schurFock_of_steps unitary_haar_measure (schurOrth_of h evaluation_at_one)

end PI.WSF
