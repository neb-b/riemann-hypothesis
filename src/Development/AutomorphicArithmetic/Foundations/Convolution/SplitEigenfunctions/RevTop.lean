module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Dens
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MomKill
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0003

@[expose] public section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem maj_holds : Maj := maj latSum decE

theorem meanZero_holds : MeanZero := meanZero decE

theorem thetaConstantTerm_eq : ThetaLiftEqAnisotropicPart := f0Eq maj_holds thCont meanZero_holds (rank1 decE maj_holds orb1)

theorem rev_holds : Rev :=
  rev thetaConstantTerm_eq (coef maj_holds thCont) (thetaPairing_constantTerm_cuspidal maj_holds thCont thetaConstantTerm_eq (coef maj_holds thCont)) dens (fub maj_holds thCont)
    (coefPer decE maj_holds orbS momKill (orbFn orbS))

end UpperTheory.ConvolutionTheory.RankTwoDescent
