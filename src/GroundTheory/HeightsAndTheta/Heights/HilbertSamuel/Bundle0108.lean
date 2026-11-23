module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0013
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntB
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageChi
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.SupStMonoNormSqPos
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.GaussSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjectionBounds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFSExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealGramComparison
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiBounds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiIndex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0105
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0088
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0097
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockImageChi.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.proof

theorem ResChiBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.proof ResolutionSupBound.full

theorem ProjectionBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.proof ResChiBounds.full

theorem PullFSExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.proof ProjFrameBasePtFree.full

theorem RealGramComparison.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.proof ResolutionSupBound.full ProjectionBounds.full PullFSExtension.full

theorem ResChiIndex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.proof

theorem VeroneseMonoBasis.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.proof

theorem ResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.proof

theorem Closed.Inter.pullbackPushforward_holds : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.proof Closed.Inter.BlockGenFinite Closed.Inter.FibreIsolFinite

theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

