module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Formalism.PeriodIntegrals.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.SiegelMeasureDefinition
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.SigmaStarEx
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TwistedEisensteinOfRemaining
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TestFunctionPeriodicity
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaUnitary.NatWCastReal

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmStar
section
theorem quantum_minor_star : PI.QmStar :=
  PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
section
theorem quotient_product_compact : PI.QuotProdK.QuotProdK :=
  QPK.quotProdK_of QPK.weil_quotient_global_assumptions QPK.haar_measure_uniqueness
    (QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition QPK.bruhat_decomposition'
      QPK.local_weil_representation)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarEx
section
theorem sigma_star_exists : PI.SigmaStarEx := PI.SSE.sigmaStarEx
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover
section
theorem transference_covering : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
section
theorem transference_successive_minima : PI.TransferenceMinima :=
  PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwistedEisensteinNonvanishing
section
theorem TwistedEisensteinNonvanishing : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing :=
  PI.TwistedEisensteinNonvanishing.W.twisted_eisenstein_of_remaining PI.TwistedEisensteinNonvanishing.W.test_function_support PI.TwistedEisensteinNonvanishing.W.test_function_periodicity PI.TwistedEisensteinNonvanishing.W.bounded_matrix_entries
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForU
section
theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := PI.WeylForUWork.weylForU_of
end

