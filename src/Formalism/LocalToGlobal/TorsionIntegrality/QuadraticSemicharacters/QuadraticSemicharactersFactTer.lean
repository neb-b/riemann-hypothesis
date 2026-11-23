module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ScalePairMulMulEq

@[expose] public section

namespace Formalism.L2.Th1.H

theorem stdDataCm : StdDataCm := StdDataCm_proof
theorem kernelRatio : KernelRatio := KernelRatio_of unitaryConstant

theorem quadraticSemicharacters_of_fact (hL : LocalStandard) (hκ : KappaExists) : quadraticSemicharacterIdentityReformulated := quadraticSemicharacterIdentityReformulated_of_kernelRatio_of_localStandard_of_kappaExists kernelRatio hL hκ

end Formalism.L2.Th1.H
