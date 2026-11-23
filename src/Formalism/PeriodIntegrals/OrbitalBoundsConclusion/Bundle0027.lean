module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
public import Formalism.PeriodIntegrals.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.SchurFockOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasWCore
section
theorem weil_measure_compat : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  PI.UnitaryGroupMassFormula.MeasWCore.measWCore_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PairCorankPos
section
theorem pair_corank_pos : PI.PairCorankPos.CorankPosG := PI.PairCorankPos.W.corankPosG
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SchurFock
section
theorem schur_fock : PI.SchurFock := PI.WSF.schurFock_of highest_weight_irreducible
end

