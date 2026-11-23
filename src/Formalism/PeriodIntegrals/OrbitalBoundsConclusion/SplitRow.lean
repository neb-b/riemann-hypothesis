module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.Bundle0004

@[expose] public section

theorem split_row_iso : PI.SplitRow.SplitRow := PI.SRW.splitRow_of_iso PI.SRW.measure_isomorphism_at_infinity
