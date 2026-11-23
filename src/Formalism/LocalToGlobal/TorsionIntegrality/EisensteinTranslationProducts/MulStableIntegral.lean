module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0006
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0007
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenySigma
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly

@[expose] public section

namespace Formalism.L2.Th1.F

theorem latticeOnly : LatticeOnly := lattice_only
theorem homogeneity : Homogeneity := homogeneity_thm
theorem kerRepsExist : KerRepsExist := kernel_reps_exist
theorem kerRepsCard : KerRepsCard := kernel_reps_card
theorem mulStableIntegral : MulStableIntegral := mul_stable_integral
theorem isogenyP : IsogenyP := isogenyWeierstrassP_of_ellipticNoPole ellipticNoPole
theorem pSecond : PSecond := weierstrass_p_second_derivative
theorem isogenySigma : IsogenySigma :=
  isogenySigma_of ellipticNoPole sigmaOrder sgStarAdd sgStarQuasi sgStarBasic kerRepsCard sigmaEntire
theorem translateProduct : TranslateProduct := translateProduct_of sgStarAdd
theorem halfShift : HalfShift := halfShift_of sigmaAdd sigmaQuasi sigmaZero pInjective
theorem cmThetaEq : CmThetaEq := cm_theta_eq
theorem cmStable : CmStable := cm_stable
theorem cmNorm : CmNorm := cm_norm

end Formalism.L2.Th1.F
