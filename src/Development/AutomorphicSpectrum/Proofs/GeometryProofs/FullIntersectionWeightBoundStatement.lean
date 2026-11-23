module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionWeightBound
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_intersection_weight_bound : GlobalTheory.CompanionTheory.Ar.Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ t : ℝ, ENNReal.ofReal (T.vol b * Top.flagDeg (reW u) * (T.slope II B b (reW u) + t)) ≤ GlobalTheory.CompHt.countVol (Top.dimFl (CMType H) (Dw.p + Dw.q)) (T.M B b).δ 8 fun τ => (modelSmall (o.toTowerOrigin.Or B b) (τ • u) (Real.exp (τ * t))).encard := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.volume_ge_slope | exact GlobalTheory.CompanionTheory.Ar.Plug.volume_ge_slope | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.volume_ge_slope <;> assumption)
