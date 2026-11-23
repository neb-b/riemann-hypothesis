module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bridge
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Universal

@[expose] public section

namespace Formalism.L2.Th1.F

theorem wpNumDen : WpNumDen := weierstrass_numerator_denominator
theorem pOfIsWp : POfIsWp := weierstrass_p_of_series
theorem pOfLattice : POfLattice := weierstrass_p_of_lattice
theorem curveBridge : CurveBridge := curve_weierstrass_series_eq
theorem hasCMByIsogeny : HasCMByIsogeny := hasCMByIsogeny_of' isogenyFormulaInstance

end Formalism.L2.Th1.F
