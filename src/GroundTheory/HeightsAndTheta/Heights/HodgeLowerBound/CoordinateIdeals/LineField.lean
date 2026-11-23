module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

abbrev L : Type := FractionRing (MvPolynomial (Fin 2) ℚ)

def xL (i : Fin 2) : L := algebraMap (MvPolynomial (Fin 2) ℚ) L (X i)

def u : L := xL 1 / xL 0

abbrev Ω : Type := ↥(IntermediateField.adjoin ℚ ({u} : Set L))

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
