module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodDatumParameters
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
theorem _root_.GlobalTheory.T.good_datum_parameters : Top.Given → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : GlobalTheory.CovTop.Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → (∃ h e', CompLaws Y.U h e') ∧ (∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p) ∧ (T.Q.Dw j).q = D.R.m - j ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ Fintype.card (CMType T.Q.H) = D.R.f ∧ hostRd D.host.E = D.host.rdE ∧ hostLval T.Q.H = dlogL D 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.vs_laws | exact GlobalTheory.CompanionTheory.Ar.Plug.vs_laws | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.vs_laws <;> assumption)
