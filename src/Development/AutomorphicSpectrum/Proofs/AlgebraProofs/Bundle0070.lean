module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0068
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibreavg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenCone
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem setCrofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  intro n e δ h W f hW hf hδ A hA hAs
  have hle : e + 1 ≤ n := chowGroups_le hW hf hδ
  have hδpos : 1 ≤ δ := ChowDegreePos.proof n (e + 1) δ W f (Nat.succ_pos e) hW hf hδ
  have hfib := ConeFibreDegree.full n e δ h W f hW hf hδ
  have hfin : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)),
      fibreCount h W π w ≠ ⊤ := by
    filter_upwards [hfib] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top δ
  obtain ⟨K, hK0, hKtop, hK⟩ := _root_.PositivityTheory.Xgn.t_xgz_chow_mahler_fibreavg n (e + 1) (Nat.succ_pos e) hle
  have hball : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤ :=
    ConeBallFinite.full n e h W f hW hf
  have hmass : ∀ B : Set (EuclideanSpace ℂ (Fin n)),
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} < ⊤ := fun B =>
    lt_of_le_of_lt (measure_mono (show _ ⊆ coneBall h W from fun y hy => And.intro hy.1 hy.2.1)) hball

  have key : ∀ B : Set (EuclideanSpace ℂ (Fin n)), IsOpen B → IsScaleStable B →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
          cntOver (coneSet h W ∩ B) π (firstCoordVec (e + 1)) =
      K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} := by
    intro B hB hBs
    have h1 := hK h W hW hfin B hB.measurableSet
      (fun y hy t ht => by
        have := hBs y hy (t : ℂ) (by exact_mod_cast ht.ne')
        simpa using this) (hmass B)
    have h2 := _root_.PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce n e (coneSet h W ∩ B)
      ((isScaleStable_coneSet h hW).inter hBs) (isSigmaCompact_cone_inter h W hB) id measurable_id
    simp only [id] at h2
    rw [← h2, h1]
  have hΓ : gaussM (e + 1) n Set.univ = ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π := by
    rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcnt : ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
      cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ * (δ : ℝ≥0∞) := by
    rw [hΓ, ← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top δ)]
    refine lintegral_congr_ae ?_
    filter_upwards [_root_.GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ] with π hπ
    have : cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) = (δ : ℝ≥0∞) := by
      rw [Set.inter_univ, cntOver]
      have : (ptsOver (coneSet h W) π (firstCoordVec (e + 1))).encard = δ := hπ
      rw [this]
      simp
    rw [this]
  have hcb : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ Set.univ} = coneBall h W := by
    ext y
    simp [coneBall, coneSet]
  have hmf : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) =
      (δ : ℝ≥0∞) * planeMass n e :=
    ConeMassOfFibre.full n (e + 1) δ h W hW hfib
  have hV0 : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top δ

  have hVΓ : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * gaussM (e + 1) n Set.univ =
      K * planeMass n e := by
    have h0 := key Set.univ isOpen_univ (fun _ _ _ _ => Set.mem_univ _)
    rw [hcnt, hcb, hmf] at h0
    refine (ENNReal.mul_left_inj hδ0 hδtop).1 ?_
    rw [mul_assoc, h0]
    ring
  have hA1 := key A hA hAs
  refine (ENNReal.mul_right_inj hV0 hVtop).1 ?_
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * (planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)))
      = planeMass n e * (volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1))) := by ring
    _ = planeMass n e * (K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A}) := by rw [hA1]
    _ = (K * planeMass n e) * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by ring
    _ = _ := by rw [← hVΓ]; ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependent
section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagModelValue


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem main : FlagModelValueIndependence.Statement :=
  FlagModelValueIndependence.proof
    (FlagPairValueIndependence.proof _root_.GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main _root_.GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent)
    (_root_.GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelCommonModel.proof
      GlobalTheory.CompanionTheory.CommAlg.joinTwoModels
      GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt.main
      GlobalTheory.CompanionTheory.Heights.join_vertical_divisor_statement
      _root_.GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main _root_.GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main)

end GlobalTheory.CompanionTheory.CommAlg.FlagModelValue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamilyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_chart_family : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (P : Out.PolAV (Geo.Tor.Sp O)), 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O) (pt : Nb p g → (sp (R₀ := O) O ⟶ P.A)), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ (∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧ IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧ ∀ (a : OE) (t : TT p g), pt (red p g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p g t) ≫ o.act a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act | exact GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act <;> assumption)
end

