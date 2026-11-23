module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
public import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.DegreeFormula.PointDegree.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Formalism.SharpRestriction.Divisibility.AdmissibleRank.FreeFamilyOfLeavesAndAdmissible
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions Formalism.MainNotions

theorem top2c2_dlSize (eps : ℝ) (Fm : FamP eps) : J.DlSize Fm := by
  unfold J.DlSize
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx1 i
  obtain ⟨-, -, -, -, -, h, -⟩ := hQD
  exact h

end Formalism.MainNotions.DIV.Proofs
