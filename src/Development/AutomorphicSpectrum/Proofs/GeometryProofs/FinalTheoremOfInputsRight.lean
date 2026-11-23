module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0257
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0246
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerVolumeTheoremStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0266
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0202
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0226
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0071

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem goodTower_volume_of_reduced : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → ThetaUnifAV → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hM hKF hSA hNS hResK hFHT hGaga hLLD hPB hHS hAn hNine hPts hAvoid hQ hZ hTheta
  have hGiven : Top.Given :=
    ⟨hM, hKF, hSA, hNS, hResK, _root_.GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds, hFHT, hGaga,
      (_root_.GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel hLLD).1, hPB, hHS, hAn, hNine,
      GlobalTheory.T.antisymmetric_perturbation_holds⟩
  have hW : Out.WeilSt := GlobalTheory.CompanionTheory.Ar.Link.weilSt
  have hHTD : GR.HodgeTateDatumStatement := GlobalTheory.CompanionTheory.Ar.GR.Top.main
  have hOrd : GR.OrdinaryCurveStatement := _root_.GlobalTheory.CompanionTheory.Ar.Link.ordinaryCurveStatement
  have hFam : Num.FamilyExistsPos := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds hFHT hQ hZ hHTD hOrd
  have hCmpSt : Cmp.CmpSt := _root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance hPB hAvoid hResK
  have hTied : HodgeComparisonCompatibility := _root_.GlobalTheory.CompanionTheory.Ar.CmpTied.cmpHodgeTied
  have hPair : Cmp.CmpPair := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair hPB hCmpSt hTied hTheta
  exact GlobalTheory.T.good_tower_volume_theorem hGiven hPts hAvoid hW hFam hPair

end GlobalTheory.CompanionTheory.Ar.Top
