module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.IndexEqOfTraceInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0003
public import Mathlib
public import Formalism.PeriodIntegrals.GZeroLogBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearCardBound.ZeroLogBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.HermitianAlgebraGeneration
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.SecondCapelliMinorContinuousLinear
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.RadialDecompositionOfParts
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq
section
noncomputable section

namespace PI

theorem adelic_index_eq : PI.AdIndexEq.IndexEq :=
  PI.UnitaryGroupMassFormula.AdIndexEq.indexEq_of_traceInt PI.UnitaryGroupMassFormula.AdIndexEq.trace_integral'

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GZeroLogBound
section
theorem GZeroLogBound : PI.GZeroLogBound.Target := PI.GZeroLogBound.UnitaryGroupMassFormula.target
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnHermHaar
section
theorem qnHermHaar : Formalism.FourierDecayAlt.Q.HermHaar :=
  PI.QnHermHaar.qnHermHaar_of_alg PI.QnHermHaar.hermitian_algebra_generation qnRdSkew quantum_minor_star
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    quantum_minor_move.1 quantum_minor_move.2 qnYLeibniz qnEabGl qnEabPres
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres
section
theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RadialDecompositionOfParts
section
theorem radial_decomposition_of_parts : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.radial_decomposition_of_parts'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqPairLocal
section
theorem square_pair_local : PI.SqPair.PLocalAll := PI.SqPairLocal.sqPairLocal_of local_cartan_pair
end

