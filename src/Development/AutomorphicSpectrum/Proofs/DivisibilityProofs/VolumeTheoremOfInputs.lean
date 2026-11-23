module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0149
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0091
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerI5
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFifthCondition
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalConditionsStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM1Nef
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalExtra
public import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelRealTowerSmooth
public import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFinalCondition
public import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelRealTower
public import Development.WeilBound.CoreStatements.VolumeEquality.VolEqOfIsFullIntersectionSystem
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerA1
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SlopeLowerBaseSettings
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0263
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem slopeLower_mono_top {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : Top.RootTower Ψ N)
    (II : IntersectionSystem) {C C' rd Lval : ℝ} (hCC : C ≤ C') (hrd : 1 ≤ rd) (hP : T.Proportional)
    (h : T.SlopeLower II C rd Lval) : T.SlopeLower II C' rd Lval := by
  intro B hB hB' hbad
  have h1 := h B hB hB' hbad
  have hJ : 0 < Top.testDeg Ψ N T.j := (_root_.GlobalTheory.CompanionTheory.Ar.Top.testPoly_facts Ψ N T.j T.j_pos T.j_lt).2.1
  have hvol : 0 ≤ T.volT := Finset.sum_nonneg fun c _ => (hP.1 c).le
  have hB1 : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hL : 0 ≤ Top.bigLam B rd Lval := by
    unfold Top.bigLam
    have h2 : (1 : ℝ) ≤ B * rd := by nlinarith
    have := Real.log_nonneg h2
    positivity
  have hK : 0 ≤ (Fintype.card Ψ : ℝ) * ((min T.j (N - T.j) : ℕ) : ℝ) * Top.bigLam B rd Lval *
      (((Top.dimX Ψ N T.j : ℝ) + 1) * (T.volT * Top.testDeg Ψ N T.j)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hCC hK]

theorem volumeTheoremX_of_inputs : Top.Given → PtsIntegrableStatement → Out.WeilSt → (∃ Ch Cu : ℝ, NineGeoU Ch Cu) →
    HodgeLatticeFlagBound → TrivFlagOnHodge → Fl.FlatDegree → TwistAut → Cmp.CmpPair → Cmp.CmpSt → Top.VolumeTheoremX := by
  intro hG hPts hW hNineE hM3 hTF hFD hTw hCP hCS
  obtain ⟨Ch, Cu, hNine⟩ := hNineE
  obtain ⟨-, -, -, -, -, -, -, -, -, hIn, hHS, -, hNF, hAP⟩ := id hG
  obtain ⟨hZ1, hZ2, -⟩ := hHS
  obtain ⟨hZh, -, -, -, hGr⟩ := hNF
  have hAg := _root_.GlobalTheory.CompanionTheory.Ar.PB.agreementPos
  refine ⟨2 * max (Ch + Cu / 2) 0 + 3 * 4 + 5, by positivity, ?_⟩
  intro E _ _ _ _ H D Xo l c Y _ T o II hGl hX hII hq hpq hbad
  obtain ⟨hrd, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  haveI := hne
  have hp : 1 ≤ D.p := by omega
  have hqp : D.q ≤ D.p := by omega
  have hUnif := _root_.RootFieldNumerics.global_model_real_tower hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hProp : T.Proportional := _root_.GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif _root_.GlobalTheory.CompanionTheory.Ar.PB.proportional hIn II hII _ _ T _ hUnif
  have hCI := _root_.GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 hAg hIn II hII _ _ T (Top.realOf o.toTowerOrigin)
  have hI1 := _root_.GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked _root_.GlobalTheory.CompanionTheory.Ar.PB.Top.coefficients hAg hIn II hII _ _ T _
    (_root_.RootFieldNumerics.global_model_real_tower_smooth hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hPos : (Top.realOf o.toTowerOrigin).Pos := fun a => (o.Fx a).pos
  have hA1 := _root_.GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower hIn II hII _ _ T _ o.smooth o.flat hPos
  have hM1 := _root_.GlobalTheory.CompanionTheory.Ar.Top.or_m1nef hG E H D Xo l c Y T o II hGl hII hp hq
  have hM2 := _root_.GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower hG E H D Xo l c Y T o II hGl hII hp hq
  have hAN : T.ANef := fun B a => _root_.GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg _ _ (T.M B a) fun k => by
    obtain ⟨h1, h0⟩ := (o.Or B a).A_deg
    by_cases hk : k = (o.Or B a).k₀
    · rw [hk, h1]; norm_num
    · rw [h0 k hk]
  have hI56 := _root_.RootFieldNumerics.global_model_tower_fifth_condition hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hI7 : T.I7 := fun B a =>
    ⟨(_root_.GlobalTheory.CompanionTheory.Ar.Top.rt_nefgen _root_.GlobalTheory.CompanionTheory.Ar.PB.nefPol hIn II hII _ _ T _ o.smooth o.flat B a).1,
      (_root_.GlobalTheory.CompanionTheory.Ar.Top.rt_nefgen _root_.GlobalTheory.CompanionTheory.Ar.PB.nefPol hIn II hII _ _ T _ o.smooth o.flat B a).2,
      GlobalTheory.T.good_tower_real_conditions hG E H D Xo l c Y T o II hGl hX hII hp hq B a⟩
  have hI8 := _root_.GlobalTheory.CompanionTheory.Ar.Top.full_intersection_tower_I8_relation hCS hG hW E H D Xo l c Y T o II hX hII hp hq
  obtain ⟨φ, hfs, hLk⟩ := GlobalTheory.T.good_tower_global_conditions hCS hAg hM3 hTF hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hP6 := _root_.GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower _ _ T II hII.1 hProp φ hLk
  have hPA := _root_.GlobalTheory.CompanionTheory.Ar.Top.propA_of_goodOrigin hAg hTw hCP hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp' => ((o.bad_iff p).1 hp').1
  have hPF := _root_.GlobalTheory.CompanionTheory.Ar.Flat.propFTop hPts hIn.2.2.1.2 hIn.2.1.2.1 _ _ T II _ (hostRd E) (hostLval H) hII.1 hCI.1 hProp hP6
    (by linarith) hbadP (_root_.RootFieldNumerics.global_model_tower_final_condition hFD hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hVol := _root_.SheetDecomposition.volEq_of_isFullIntersectionSystem hCS hG E H D Xo l c Y T o II hGl hX hII hq hpq
  have hj3 : 3 * (D.p + D.q - T.j) + 1 ≤ D.p + D.q := by rw [o.j_eq]; omega
  have hSL0 := _root_.GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings hZh II hII.1 _ _ T Ch Cu (hostRd E) (hostLval H) hProp hj3
    fun B _ hB _ a => GlobalTheory.T.base_setting_of_good_tower Ch Cu hNine hW hAg _root_.GlobalTheory.CompanionTheory.Ar.PB.proportional hCS hG hPts E H D Xo l c Y T o II hGl hX hII
      hp hq hqp hbad B hB a
  have hSL := slopeLower_mono_top T II (le_max_left (Ch + Cu / 2) 0) (by linarith) hProp hSL0
  have hch := _root_.GlobalTheory.CompanionTheory.Ar.Top.chain_tower _root_.GlobalTheory.CompanionTheory.Ar.PB.flagHeight_holds hIn hZ1 hZ2 hAP hGr II hII _ _ T _ (max (Ch + Cu / 2) 0) 4 (hostRd E)
    (hostLval H) (le_max_right _ _) (by norm_num) (by linarith) hfs hProp hI1 hCI.2 hA1 hM1 hM2 hAN hI56.1 hI56.2
    hI7 hI8 hP6 hPA hPF hVol hSL
  exact ⟨hProp, hVol, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
