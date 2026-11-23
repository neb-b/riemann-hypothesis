module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0067
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem selfIntersection_le_of_boundedInjection_use :
    PositivityTheory.MbHsUse.HSUse → MoriwakiBigStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G3.Statement :=
  fun hU hBig =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.G3.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hBig)
      hU.g7 _root_.GlobalTheory.CompanionTheory.Ar.Small.packing

end GlobalTheory.CompanionTheory.Ar.Giv
