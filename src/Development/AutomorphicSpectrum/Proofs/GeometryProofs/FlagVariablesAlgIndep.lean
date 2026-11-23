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
public import Development.WeilBound.CoreStatements.HodgeTatePoints.QakReindex

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_variables_alg_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K L : Type) [Field K] [Field L] [Algebra K L] (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) L), AlgebraicIndependent K (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) → ∃ T : FlagVar Dw → L, AlgebraicIndependent K T ∧ Set.range T = Set.range (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ ∀ (s : CMType H ⊕ CMType H) (i j : Fin (Dw.mult (Small.labelC s))) (hij : i < j), T ⟨Small.labelC s, ⟨(i, j), hij⟩⟩ = v s (Fin.cast (Small.mult_labelC Dw s) j) (Fin.cast (Small.mult_labelC Dw s) i) := by
  first | exact @PositivityTheory.HtPt.Qak.reindex | exact PositivityTheory.HtPt.Qak.reindex
