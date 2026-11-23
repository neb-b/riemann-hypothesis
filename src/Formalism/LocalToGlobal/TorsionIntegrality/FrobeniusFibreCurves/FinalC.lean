module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0004

@[expose] public section

namespace Formalism.L2.Th1.B

theorem baseChange : BaseChange := Map.baseChangeCompatible
theorem curveSigma : CurveSigma := Crv.curve_sigma_function_holds
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := Crv.curve_formal_first_level_holds

end Formalism.L2.Th1.B
