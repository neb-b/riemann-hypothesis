module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseBoundedHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightComparison.main : HeightComparison.Statement := heightComparison

theorem DenseBoundedHeight.main : DenseBoundedHeight.Statement := denseBoundedHeight

theorem SlopeMaxExtension.main : SlopeMaxExtension.Statement := slopeMaxExtension

end GroundTheory.Heights₂.Heights
