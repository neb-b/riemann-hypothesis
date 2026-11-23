module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineMu
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0006

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Metric
open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)

def refOne : HermLine (PBlk 2) := HermLine.ofWeight (fun _ => 0) fun _ _ _ => rfl

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
