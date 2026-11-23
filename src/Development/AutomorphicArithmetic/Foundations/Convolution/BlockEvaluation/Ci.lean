module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.KillEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.OneSide
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TrOnBot
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwInt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspTrBand

@[expose] public section


open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.Ci in
theorem UpperTheory.ConvolutionTheory.ci : UpperTheory.ConvolutionTheory.CI :=
  ciOf (trExp expForm) (evVal evEx Dp.parEx) valBc (killEx Dp.parEx) kfBc truncSpec sepPoly
    (oneSide K.kern2 C.polyBdAll C.smoothDecay C.decayTraceClass C.cuspTrBand Dp.multiplicity_one_cuspidal_spectrum_normOneGL evEx) evEx kill
