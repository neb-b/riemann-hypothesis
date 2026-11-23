module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CoordCurveDegree
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def CoordCurveDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 →
      degC (mCoordIdeal y) = Nat.card (blockFnField y →ₐ[ℚ] ℂ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveComplexPoint
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveComplexPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)),
    IsArithVar W 1 → (mcPts W).Nonempty

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveIsOrbit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def CurveIsOrbit.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (W : Ideal (MvPolynomial (Coord n) ℤ)),
    Geo.IsArithVar (ι := blockIdx n) W 1 →
      ∃ x : Cone n (AlgebraicClosure ℚ), BlockNonzero x ∧ W = orbitIdeal x

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveDivVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ), IsArithVar W 1 → IsMultiHomog s a → s ∉ W →
    ∀ V ∈ divSupp W s, ¬ IsHorizontal V

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
end

