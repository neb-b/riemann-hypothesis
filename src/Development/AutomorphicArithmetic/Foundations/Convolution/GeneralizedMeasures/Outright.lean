module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit

@[expose] public section

theorem UpperTheory.ConvolutionTheory.GM.gm : UpperTheory.ConvolutionTheory.GM.GM := UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit
