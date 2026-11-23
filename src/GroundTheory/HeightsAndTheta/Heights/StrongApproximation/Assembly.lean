module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PTruncation

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.StrongApprox

theorem AETopologicalRing.full : AETopologicalRing.Statement := AETopologicalRing.proof

theorem HypPairExists.full : HypPairExists.Statement := HypPairExists.proof

theorem EDenseInAE.full : EDenseInAE.Statement := EDenseInAE.proof AETopologicalRing.full

theorem OrthProjection.full : OrthProjection.Statement := OrthProjection.proof AETopologicalRing.full

theorem EichlerDense.full : EichlerDense.Statement :=
  EichlerDense.proof AETopologicalRing.full EDenseInAE.full OrthProjection.full

theorem ClosureIsSubmonoid.full : ClosureIsSubmonoid.Statement :=
  ClosureIsSubmonoid.proof AETopologicalRing.full EichlerDense.full

theorem LocalRingHypotheses.full : LocalRingHypotheses.Statement := LocalRingHypotheses.proof

theorem PlaceMaps.full : PlaceMaps.Statement := PlaceMaps.proof LocalRingHypotheses.full

theorem EichlerAtPlace.full : EichlerAtPlace.Statement := EichlerAtPlace.proof PlaceMaps.full

theorem LocalInClosure.full : LocalInClosure.Statement :=
  LocalInClosure.proof HypPairExists.full ClosureIsSubmonoid.full LocalRingHypotheses.full
    PlaceMaps.full EichlerAtPlace.full

theorem Truncation.full : Truncation.Statement := Truncation.proof LocalInClosure.full

theorem AENeighbourhoods.full : AENeighbourhoods.Statement :=
  AENeighbourhoods.proof AETopologicalRing.full PlaceMaps.full

theorem SAHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAStatement :=
  SAHolds.proof HypPairExists.full AENeighbourhoods.full Truncation.full

theorem SAOpenHolds.full : ReciprocityTheory.ChartRestriction.G.SA.SAOpenStatement :=
  SAOpenHolds.proof SAHolds.full AETopologicalRing.full

end GroundTheory.Heights₂.Heights.StrongApprox
