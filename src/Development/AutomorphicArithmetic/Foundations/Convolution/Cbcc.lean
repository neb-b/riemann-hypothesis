module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CbccOfUnit
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit

@[expose] public section

theorem UpperTheory.ConvolutionTheory.cbcc : UpperTheory.V.Z.Bc.CBCc :=
  UpperTheory.ConvolutionTheory.cbcc_of_unit PositivityTheory.Rg.Tf.Loc.bcflUnit
