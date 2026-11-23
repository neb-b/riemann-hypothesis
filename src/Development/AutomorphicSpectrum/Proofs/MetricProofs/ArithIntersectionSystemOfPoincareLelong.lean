module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelongStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I4

theorem contractMixed_closed : ContractMixedStatement :=
  have hIntZero : Inter.PFIntZero.Statement :=
    Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)
  have hVert : Inter.PFVert.Statement :=
    Inter.PFVert.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _) Targets.contractMixedField
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    hIntZero hVert

theorem arithIntersectionSystem_of_poincareLelong_resK :
    GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement := fun hPL hRK =>
  Targets.ArithIntersectionSystem.of_found
    (GlobalTheory.T.intersection_exists_of_poincare_lelong hPL (_root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hRK))
    (_root_.GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord (_root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hRK)).2
    contractMixed_closed

end GlobalTheory.CompanionTheory.Ar.Pub
