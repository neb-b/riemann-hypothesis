module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle0003

@[expose] public section

theorem adUnimod_closed : PI.AdUnimod :=
  PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable PI.adelic_index_eq
