module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.LubinTateLogIsArtinHasse
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Formalism.GaussJetBounds.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0002

@[expose] public section

namespace Formalism.L2.Th1.D

theorem phCompare : PhCompare := phi_comparison
theorem first_level_on_curve : CurveExponentCoboundaryCocycle := first_level_curve_holds
theorem fieldDataCM : FieldDataCM := complex_multiplication_field_data
theorem gramExists : GramExists := gram_matrix_exists

end Formalism.L2.Th1.D
