module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0009
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0008
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IntegerEndomorphismInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
section
namespace Formalism.L2.Th1.F

theorem hasCMByStable : HasCMByStable := has_cm_stable
theorem hasCMByScale : HasCMByScale := has_cm_scale
theorem cmPairHasCMBy : CmPairHasCMBy := cm_pair_has_cm
theorem jInvScale : JInvScale := j_invariant_scale
theorem seriesScale : SeriesScale := series_scale
theorem sigmaScale : SigmaScale := sigma_scale'
theorem seriesMap : SeriesMap := series_map

end Formalism.L2.Th1.F
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
section
namespace Formalism.L2.Th1.F

theorem taylorRing : TaylorRing := taylor_ring
theorem taylorDeriv : TaylorDeriv := taylor_deriv
theorem taylorExp : TaylorExp := taylor_exp
theorem taylorSigma : TaylorSigma := taylorSigma_of taylorRing taylorDeriv
theorem taylorSgStar : TaylorSgStar := taylorSgStar_of taylorSigma taylorRing taylorExp sigmaEntire
theorem pSeriesCoeff : PSeriesCoeff := weierstrass_p_series_coeff
theorem taylorIsWp : TaylorIsWp := taylorIsWp_of taylorRing taylorDeriv
theorem isWpUnique : IsWpUnique := weierstrass_series_unique
theorem endoZInstance : EndoZInstance := integer_endomorphism_instance
theorem isogenyFormulaInstance : IsogenyFormulaInstance := isogeny_formula_instance

end Formalism.L2.Th1.F
end

