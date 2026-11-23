module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionRepresentation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem torsRep_nonempty_of_relAmple : ∀ (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ), 1 ≤ p → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Nonempty (TorsRep A p) :=
  PositivityTheory.HtPt.Rg.torsrep_ex

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisor
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.CutClosed

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem verticalPush : BlowUpVerticalPush.Statement.{0} :=
  BlowUpVerticalPush.proof (BlowUpVerticalFibre.proof BlowUpModel.full
    (BlowUpFibreDegree.proof NumbersDVR_HomLocRingLocal NumbersDVR_DivCycleHomLoc
      FiniteBirationalLength.full _root_.GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main) _root_.GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree)

theorem main : CutByEffectiveDivisor.Statement.{0} :=
  CutByEffectiveDivisor.of_steps NumbersDVR_C3NoCommon
    (CommonFactorInduction.of_open ReesAlgebraDim.full BlowUpStrictTransform.proof
      NumbersDVR_C3BlowUpExcessDrop verticalPush (BlowUpDivisorPush.proof verticalPush)
      NumbersDVR_BlowUpHorizontalCorresp HorizontalComponentModel.proof)

end GlobalTheory.CompanionTheory.Ar.Num.CutClosed
end

