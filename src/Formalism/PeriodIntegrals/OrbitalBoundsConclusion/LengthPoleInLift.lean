module

public import Formalism.PeriodIntegrals.LengthPoleInLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PoleLengthBound

@[expose] public section

theorem length_pole_t0 : PI.LengthPoleInLift := PI.PoleLengthCount.pole_length_bound
