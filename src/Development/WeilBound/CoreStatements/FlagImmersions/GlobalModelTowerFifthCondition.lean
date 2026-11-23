module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0267
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0259
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0250
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0010

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem global_model_tower_fifth_condition : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II _ _ hII hp _
  have hG' := hG
  obtain ⟨-, -, -, -, hRes, -, hF, hGaga, -⟩ := hG'
  refine _root_.GlobalTheory.CompanionTheory.Ar.TopGood.tower_good_of_sandwich_split hG (GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga) E H D l (Xo l) c Y T o II hII.1
    (splitComps_of_origin o.toTowerOrigin) fun B a p hpS => ?_
  haveI : Fact p.Prime := ⟨(o.Or B a).𝔐.S_prime p hpS⟩
  exact _root_.GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree hF E H D l (Xo l) c _ _ Y (o.S B) _ _ _ _ (o.Or B a).𝔐 p hpS (by omega) (o.omVB B a p hpS)

end RootFieldNumerics
