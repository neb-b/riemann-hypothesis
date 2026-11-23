module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CountVolumePowerComparison
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
theorem _root_.GlobalTheory.T.count_volume_power_comparison : ∀ (D n d k₀ : ℕ) (m m' : ℕ → ℕ∞), 0 < n → 0 < d → 8 ∣ k₀ → (∀ᶠ τ : ℕ in atTop, m τ ≤ m' (τ + k₀) ^ d) → GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ GlobalTheory.CompHt.countVol D n 8 m' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.countVol_le_of_le_shift_pow | exact GlobalTheory.CompanionTheory.Ar.Plug.countVol_le_of_le_shift_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.countVol_le_of_le_shift_pow <;> assumption)
