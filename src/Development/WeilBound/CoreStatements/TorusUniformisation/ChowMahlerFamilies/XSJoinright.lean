module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

namespace PositivityTheory.Xgn.A_s_joinright

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.full GenericDimBound.full GenericDimGe.proof SpecialIdealCorresp.full
    SpecialIdealMultiHomog.full SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialQuotDim.full
    ComponentDim.proof

theorem pairNumRelabel : PairNumberRelabelAlt.Statement :=
  PairNumberRelabelAlt.proof (VerticalComponentFibre.proof fibreVarieties)

theorem of_pullback (h : PairNumberPullback.Statement) : FlagModelJoinRightAlt.Statement :=
  FlagModelJoinRightAlt.proof JoinVerticalDivisor.proof (FlagPairJoinRight.proof JoinVerticalDivisorRight.proof)
    (PairNumberJoinRight.proof
      (PairNumberJoinLeft.proof h JoinVerticalDivisorLeft.proof BirationalJoin.proof)
      JoinVerticalDivisorRight.proof pairNumRelabel)

end PositivityTheory.Xgn.A_s_joinright
