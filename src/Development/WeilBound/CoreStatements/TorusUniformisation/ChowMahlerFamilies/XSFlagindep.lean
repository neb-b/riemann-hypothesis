module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041

@[expose] public section

namespace PositivityTheory.Xgn.A_s_flagindep

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem closureModel : GenericProjClosureModel.Statement :=
  GenericProjClosureModel.proof TwistedDualGensExist.proof
    (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
      (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
    (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)

theorem flagClosureModel : SegreFlagClosureModel.Statement :=
  SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)

theorem of_items (hC2 : VerticalDivisorsCommute.Statement.{0}) (hPull : PairNumberPullback.Statement)
    (hCut : SegreFlagClosureCut.Statement) : FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof hC2
  have hSP := SegreFlagClosurePullback.proof hPull hPE flagClosureModel PairNumberRelabel.proof
    VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE flagClosureModel hCut hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE closureModel hSCN)
    SymmetricSpanHsymm.proof

end PositivityTheory.Xgn.A_s_flagindep
