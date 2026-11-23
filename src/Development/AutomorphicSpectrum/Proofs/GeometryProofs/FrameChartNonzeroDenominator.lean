module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.RegularChartNonzeroDenominator

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.CompanionTheory.Relay.frame_chart_nonzero_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h), ∃ g₀ : C.R, g₀ ≠ 0 ∧ ∀ (A : Subring (Om C.Z)) (hA : ∀ r : C.R, (r : Om C.Z) ∈ A), (g₀ : Om C.Z)⁻¹ ∈ A → ∀ (L : Type) [Field L] (io : c.F →+* L) (ev : A →+* L), letI := io.toAlgebra; ∀ (ψ : C.R →ₐ[c.F] L), (∀ r : C.R, ψ r = ev ⟨r, hA r⟩) → ∀ (z y : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrBor t z y → FinTr.RegAt h C.Z io A ev y := by
  first | exact @ModelDimension.regular_chart_nonzero_denominator | exact ModelDimension.regular_chart_nonzero_denominator
