module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerVolumeTheorem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_volume_theorem : Top.Given → PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → Out.WeilSt → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → Cmp.CmpPair → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hG hPts hAv hW hFam hPair
  have hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have hFHT : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hGaga : Flat.GagaSections := hG.2.2.2.2.2.2.2.1
  have hPB : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hA0 := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hGaga
  have hA1 := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga hR hGaga
  refine ⟨?_, ?_⟩
  · intro E _ _ _ H D Xo l c Y _ hgl hs hp hq
    exact GlobalTheory.CompanionTheory.Ar.TopTower.exists_good_tower hG hW hA0 hA1 E H D Xo l c Y hgl hs hp hq
  · exact GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs hG hPts hW (GlobalTheory.T.exists_geometric_height_constants hG hW _root_.GlobalTheory.CompanionTheory.Ar.Fl.flatDegree) (_root_.GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos hFam)
      (_root_.GlobalTheory.CompanionTheory.Ar.Num.trivFlagOnHodge_of_fargues hFHT) _root_.GlobalTheory.CompanionTheory.Ar.Fl.flatDegree _root_.GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut hPair (_root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance hPB hAv hR)

