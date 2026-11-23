module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CostTwoLogBound
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
theorem _root_.GlobalTheory.T.cost_two_log_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (B : ℝ), 128 ≤ B → (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ ⌊B⌋₊ → 0 ≤ costTwo l B ∧ costTwo l B ≤ 60 * (Real.log B + Real.log (hostRd E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.costTwo_bound | exact GlobalTheory.CompanionTheory.Ar.Plug.costTwo_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.costTwo_bound <;> assumption)
