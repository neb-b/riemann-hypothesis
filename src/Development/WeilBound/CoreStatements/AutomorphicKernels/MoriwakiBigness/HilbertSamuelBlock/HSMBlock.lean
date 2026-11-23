module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyConditional
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0108
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0100
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0089
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHSMTransport
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0097
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0085
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGramMono
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceIndex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulePieceHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0110
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027

@[expose] public section

namespace PositivityTheory.LocalParametersCuspidal.MB.HSM

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
  ReciprocityTheory.ChartRestriction.G.AI.I1

theorem theoremHSMBlock (hAIS : ArithIntersectionSystemStatement) (hResK : ResK.ResKStatement) :
    TheoremHSMBlock.Statement := by
  have hGr : GraphStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.graphStatement
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hRes : ResExistsStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hResK
  have hPts : PtsIntegrableStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK hResK
  have hPF : PFCoordStatement := (_root_.GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord hRes).2
  have hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι := Targets.existsUniqueAll
  have hGF : GenFibreExistsStatement := Targets.genFibreExists
  have hIso : IsomInvariance.Statement := IsomInvariance.proof (Inter.RatR.proof hPts)
  have hCM : ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr hIso GraphIsometric.proof
  have hDim : FibreDimStatement := GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
  have hDG : Inter.DegreeGeneric.Statement :=
    GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hPts (Inter.PtsAbsMeasurable.proof hRes)
  have h6 : ProjFrameGraphDeg.Statement :=
    ProjFrameGraphDeg.proof hEU ProjFrameFibrePt.full ProjFrameFibreDeg.full
  have h15 : GraphChangeOfModel.Statement :=
    GraphChangeOfModel.proof hAI3 hGr hGF hEU hIso GraphIsometricForms.full
  have h16 : BlockGraphDeg.Statement :=
    BlockGraphDeg.proof hGr BlockGraphImage.full hGF hDim hEU Closed.Inter.ChartRankAdjoin
      BlockGraphFibreRatio.full
  have h18 : VeroneseGraphDeg.Statement :=
    VeroneseGraphDeg.proof hGr VeroneseGraphImage.full hDim hEU
  exact TheoremHSMBlock.of_open TwoBlockPieceIndex.proof TwoBlockModuleFinite.proof
    ModulePieceHilbert.proof TwoBlockModuleCycle.proof hPF hCM h6
    (HSMTransport.proof KrullDimMatAct.proof)
    (ResolutionDegree.proof PullFSExtension.full ProjFSMass.proof) ResolutionMixedBridge.full
    (BlockResolutionImageSup.proof ChartSupBound.full)
    (BlockResolutionDegreeIntegral.proof (GenDegGeomDeg.proof hDG)) BlockResolutionMixedBridge.full
    hAbs BlockImageInverse.proof h15 h16 VeroneseGramMono.proof h18

end PositivityTheory.LocalParametersCuspidal.MB.HSM
