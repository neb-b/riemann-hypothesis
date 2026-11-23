module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Imports
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.ImportsBis
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.ChartRestriction.G.Geo

theorem hsLinks_of_use :
    PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement →
      ArithmeticIntersectionNonneg ∧ SuccessiveMinimaLowerBound ∧ SuccessiveMinimaUpperBound ∧ ArithmeticVolumeLowerBound ∧
        GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement ∧ GroundTheory.Heights₂.Heights.DimX.Statement := by
  intro hU hBig
  have a0 : SuccessiveMinimaLowerBound := hU.z1
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.G1.full, a0,
    GroundTheory.Heights₂.Heights.ForSecondHalf.Z2.proof hBig,
    GroundTheory.Heights₂.Heights.ForSecondHalf.BigLineBundleMoriwaki.of_moriwakiBig hBig,
    GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.proof a0,
    GroundTheory.Heights₂.Heights.DimX.proof⟩

end GlobalTheory.CompanionTheory.Ar.Giv
