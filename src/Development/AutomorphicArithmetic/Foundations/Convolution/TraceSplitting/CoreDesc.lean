module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic

@[expose] public section

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.coreDesc :
    UpperTheory.ConvolutionTheory.CI → UpperTheory.ConvolutionTheory.GM.GM → UpperTheory.ConvolutionTheory.T.CoreDesc :=
  coreDesc_of absLast pullBack unitTrace oneTerm sideSum pickS pickInf tyEx termE goodEx places C.occursBasics L1.eigBasic
