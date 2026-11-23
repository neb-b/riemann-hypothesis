module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.CoreInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.Cix
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CbccOfCore
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl

@[expose] public section

open UpperTheory.ConvolutionTheory UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs_of_gm (hG : GM.GM) : IndCs :=
  indCs (indNorm (coreInd cix hG (T.liftAll (T.liftStep (T.coreLift ci hG)))))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs_of_bcfl (h : PositivityTheory.Rg.Tf.Loc.BCFLUnit) : IndCs :=
  indCs_of_gm (GM.gm_of_bcfl h)
