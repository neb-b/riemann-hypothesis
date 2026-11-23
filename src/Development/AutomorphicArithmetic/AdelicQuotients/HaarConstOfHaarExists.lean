module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0070

@[expose] public section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology

theorem UpperTheory.haar_const_of_haar_exists :
    HaarEx → HaarConst :=
  _root_.UpperTheory.Reformulated.B.Gla1.haar_const_of_haar_exists
