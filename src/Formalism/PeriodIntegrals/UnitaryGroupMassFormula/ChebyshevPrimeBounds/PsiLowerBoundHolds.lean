module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.Bundle0001

@[expose] public section

namespace PI.PC

theorem psiUpperBound_holds : CHUpper := chUpper_of chebyshevConstantNumeric dUpper sandwich

end PI.PC
