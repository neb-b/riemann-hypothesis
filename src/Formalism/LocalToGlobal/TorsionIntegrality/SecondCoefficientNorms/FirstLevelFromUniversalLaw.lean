module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntPSDerivativeOfLG
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0003
public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntegralThirdInvariantDerivative

@[expose] public section

namespace Formalism.L2.Th1.C

theorem simeqIffCong : SimeqIffCong := simeq_iff_congruence
theorem unitBallClosed : UnitBallClosed := unit_ball_closed
theorem phOIsPh : PhOIsPh := odd_phi_is_phi
theorem first_level_from_universal_law : FirstLevelFromUniversal := first_level_from_universal_holds

theorem logDerivInt : LogDerivInt := log_derivative_integral'
theorem derivation_cube_integral_jet : ThirdJetIntegral := third_jet_integral
theorem jetsUnramified : JetsUnramified := jets_unramified
theorem jetsShape : JetsShape := jets_shape

end Formalism.L2.Th1.C
