module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.LocDensCorankOfCounts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.FieldCountHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.ResidueEqZeroIff

@[expose] public section

theorem local_density_corank : PI.LocDensCorank.LocDensCorank :=
  PI.UnitaryGroupMassFormula.LocDensCorank.locDensCorank_of_counts PI.UnitaryGroupMassFormula.LocDensCorank.fieldCount_holds
    PI.UnitaryGroupMassFormula.LocDensCorank.splitCount_holds
