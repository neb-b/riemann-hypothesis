module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.REndoOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.BadFinite
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0001

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.Zero.ConvolutionTheory.EB

theorem specP (P : Pred) (h : CuspReadP P) : Spec P := rSpec_of peakRun genSt ptOk hkMul repAlg positionTest P (rRead P h)

theorem endoP (P : Pred) (h : CuspReadP P) : EndoP P :=
  rEndo_of arEx lvEx powRep cmbTest cmbEll repAlg powNorm P (specP P h)

theorem stableP (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) (P : Pred) (h : CuspReadP P) :
    StableP P := rStable h2 h3 h5 (cmbPi h1 h4) P (specP P h)

theorem endoBlockG (h : CuspReadI) : EndoBlockG := endoG_of (endoP _ (cuspReadP_inf h))

theorem stableBlockG (h : CuspReadI) (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) : StableBlockG :=
  stableG_of (stableP h1 h2 h3 h4 h5 _ (cuspReadP_inf h))

end UpperTheory.Zero.ConvolutionTheory.EB
