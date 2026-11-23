module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0112
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCuspDataForTorusInvariant
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0255
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0029
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003

@[expose] public section

noncomputable section

namespace SheetDecomposition

open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem muMass : MuMass := by
  intro hG hP E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or hII
  classical
  have : Nonempty (CMType H) := (_root_.GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H).2.1
  obtain ⟨U, M, S, S', -, h0, ht, hS, hS', -⟩ := _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_regularisations_tied hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨Cd, rfl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight K J II _ Ω W Dc U h0 ht
  let X : ComponentSetting Dc ℤ (Fin 2 → ℤ) := ⟨Hd, Cd, M, S, hS, S', hS', 0, 0⟩
  have hA := (GlobalTheory.T.height_comparison_between_models hG hP K J II _ Ω W Dc Hd M M S S 0 hII hS hS).1
  have hL := (_root_.GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit II _ K J Ω W Dc ℤ (Fin 2 → ℤ) X 0 hII.1 hA).2
  have hSm := MuRegSmooth.proof HermExtend.proof (ProjSmoothAlong.proof HoloInjDerivInj.proof _root_.GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart)
    (VertFactorSmooth.proof VertFactorPos.proof) VertFactorPos.proof II _ K J Ω W Dc ℤ (Fin 2 → ℤ) X 0
  have hg := _root_.GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system ⟨II, hII⟩ hG.2.2.2.2.1
  refine tendsto_nhds_unique hL (tendsto_const_nhds.congr' ?_)
  filter_upwards [hSm] with t hs
  have hvert : ∀ p ∈ Dc.SB 0, p.Prime ∧ IsVerticalDivisorAt (mCoordIdeal Dc.y) p (Dc.vdeg p) (Dc.vnum p) (Dc.vden p) :=
    fun p hp => ⟨Dc.S_prime p (Finset.mem_filter.1 hp).1, Dc.vertical p (Finset.mem_filter.1 hp).1⟩
  have ha : (muReg X.H X.S 0 t).a = Hd.aMu + ∑ p ∈ Dc.SB 0, Dc.vdeg p := by
    rw [muReg, smoothRep_a]
    rfl
  rw [hg K J Ω Dc.y Dc.n _ Dc.arith hs, ha,
    VerticalTwistGenDeg.proof K J (mCoordIdeal Dc.y) Dc.n Hd.aMu (Dc.SB 0) Dc.vdeg Dc.vnum Dc.vden Dc.arith hvert]

end SheetDecomposition
