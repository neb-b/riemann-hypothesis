module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalConditions
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_global_conditions : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → PB.AgreementPos → HodgeLatticeFlagBound → TrivFlagOnHodge → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), FrobShape (fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ)) ∧ Num.LinkedTower T II φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.Link.goodOrigin_linked | exact GlobalTheory.CompanionTheory.Ar.Top.Link.goodOrigin_linked | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.Link.goodOrigin_linked <;> assumption)
