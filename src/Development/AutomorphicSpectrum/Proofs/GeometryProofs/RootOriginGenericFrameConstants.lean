module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0193
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenericFrameConstantAlgebra

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_generic_frame_constants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), letI := Small.cstAlg Or; ∀ (y' : FrPt Xo c RM.Ω), Small.ptY Y y' = Or.𝔐.ξ ≫ Or.𝔐.f → ∀ (Wv : ∀ s, Fin (labelRk Dw s) → Or.𝔐.Li) (Tm : ∀ s, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω), (∀ s k, (Or.𝔐.M.pt (Wv s k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k)) → (∀ s i, Or.Fl.b s i = ∑ m, Tm s i m • Wv s m) → (∀ s i m, i < m → Tm s i m = 0) → (∀ s i, Tm s i i ≠ 0) → ∃ t : Ix Dw → (RM.Ω)ˣ, FrBor t y' Fr.y₀ := by
  first | exact @ModelDimension.generic_frame_constant_algebra | exact ModelDimension.generic_frame_constant_algebra
