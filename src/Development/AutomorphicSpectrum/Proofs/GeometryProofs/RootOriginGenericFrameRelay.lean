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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenericFrameRootOrigin

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_generic_frame_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h) (V : ValuationSubring RM.Ω), letI := Small.cstAlg Or; ∀ (ψ : C.R →ₐ[c.F] RM.Ω) (z : FrPt Xo c RM.Ω) (d : Ix Dw → (RM.Ω)ˣ), FrMap ψ C.y z → FrBor d Fr.y₀ z → (∀ x, ψ x ∈ V) → ∀ cc : (k : RM.K) → RM.ι k, (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → (∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, cc k⟩ ∈ V) → ∀ r : RootIx Dw, ∃ v : Vˣ, ((d (Small.rootFrameIx Dw r) ^ HodgeCpt.rootSgn Dw r : (RM.Ω)ˣ) : RM.Ω) = ((v : V) : RM.Ω) * ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) * Or.e r) := by
  first | exact @ModelDimension.generic_frame_root_origin | exact ModelDimension.generic_frame_root_origin
