module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.HermitianCurvature.StatementSz
public import Formalism.HermitianCurvature.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellGeo
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdScal
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfProductFormula
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.HermitianLattices.StatementLat
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker
section

end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.GramFlagFamilyOfDetProduct
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem NE_pow (D : D7) : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) = (gS D : ℝ) ^ (D.R.m * D.R.f) := by
  unfold NE
  rw [j_finrank D, ← pow_mul]
  congr 1
  have h2 := D.R.two_le_m
  obtain ⟨k, hk⟩ := D.R.m_even
  have hm : 2 * (D.R.rS + 1) = D.R.m := by
    unfold Ranks.rS
    omega
  rw [← hm]
  ring

end Formalism.MainNotions.GramProductBounds

end
end

