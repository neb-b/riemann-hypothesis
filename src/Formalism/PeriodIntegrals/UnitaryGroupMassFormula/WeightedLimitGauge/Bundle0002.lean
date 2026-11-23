module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartJac
section
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace PI.RhsWLim.W

theorem chartJac : ChartJac := by
  intro E _ _ _ _ _ _ Φ ν δ hΦ hdet hδ hδtop hU
  obtain ⟨U, hU, hνU⟩ := hU
  have hstrict : HasStrictFDerivAt Φ
      ((ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero (fderiv ℝ Φ 0) hdet : E ≃L[ℝ] E) :
        E →L[ℝ] E) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hΦ.hasStrictFDerivAt_fderiv (by norm_num)
  have hsrc : (hstrict.toOpenPartialHomeomorph Φ).source ∈ 𝓝 (0 : E) :=
    (hstrict.toOpenPartialHomeomorph Φ).open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 1 Φ y := hΦ.eventually (by simp)
  have hUpre : Φ ⁻¹' U ∈ 𝓝 (0 : E) := hΦ.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hsrc hev) hUpre)
  have hcont : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) 0 := by
    have hA : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det|) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp (continuous_abs.continuousAt.comp
        (ContinuousLinearMap.continuous_det.continuousAt.comp (hΦ.continuousAt_fderiv (by norm_num))))
    have hB : ContinuousAt (fun x => δ (Φ x)) 0 := hδ.comp hΦ.continuousAt
    exact ENNReal.Tendsto.mul hA (Or.inr hδtop) hB (Or.inr ENNReal.ofReal_ne_top)
  have hntop : ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hδtop
  have heq : ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (Φ '' Metric.ball 0 ρ) =
      ∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x) := by
    intro ρ _ hρε
    have hsub : Metric.ball (0 : E) ρ ⊆ Metric.ball 0 ε := Metric.ball_subset_ball hρε.le
    have hinj : Set.InjOn Φ (Metric.ball 0 ρ) := by
      rw [← hstrict.toOpenPartialHomeomorph_coe]
      exact (hstrict.toOpenPartialHomeomorph Φ).injOn.mono fun x hx => (hball (hsub hx)).1.1
    have hcd : ∀ x ∈ Metric.ball (0 : E) ρ, ContDiffAt ℝ 1 Φ x := fun x hx => (hball (hsub hx)).1.2
    have hdiff : ∀ x ∈ Metric.ball (0 : E) ρ,
        HasFDerivWithinAt Φ (fderiv ℝ Φ x) (Metric.ball 0 ρ) x := fun x hx =>
      ((hcd x hx).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    have hcon : ContinuousOn Φ (Metric.ball 0 ρ) := fun x hx =>
      (hcd x hx).continuousAt.continuousWithinAt
    have hmeas : MeasurableSet (Φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hcon hinj
    have himg : Φ '' Metric.ball 0 ρ ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hball (hsub hx)).2
    rw [hνU _ himg hmeas]
    exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      Metric.isOpen_ball.measurableSet hdiff hinj δ
  have hlim := chartLim E E Φ ν (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) hcont hntop
    ⟨ε, hε, heq⟩
  have h0 : (ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0)).toReal =
      (δ (Φ 0)).toReal * |(fderiv ℝ Φ 0).det| := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), mul_comm]
  rw [← h0]
  exact hlim

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : ℂ :=
  herm (Hpk k r) (Matrix.of x *ᵥ z') z

def pairConst (k : ℕ) (T T' : ℝ) : ℝ := 2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1))

def RhsTest : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ g : ℂ → ℝ≥0∞, Measurable g →
      rhsW k r z z' μW μW' μsec (fun x => g (pairF k r z z' x)) =
        ENNReal.ofReal (a * a') * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def PairPush : Prop :=
  ∀ (k r : ℕ) (νg : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) νg →
    ∀ z z' : Fin (2 * r + k + 1) → ℂ, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (pairF k r z z' x) ∂νg = ENNReal.ofReal (pairConst k (Tz k r z) (Tz k r z')) *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def rmulM {k r : ℕ} (p : Mat k r) (x : Mt k r) : Mt k r := Matrix.of x * p

def TransW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ p ∈ UWb k r, p *ᵥ ((Real.sqrt (Tz k r z) : ℂ) • wLast k r) = z

def UnimodW : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ p ∈ UWb k r, ν.map (rmulM p) = ν

def OrbitPushG : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z' → 0 < Tz k r z' →
    ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ f : (Fin k → ℂ) × ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg =
        ENNReal.ofReal (volU k * 2 ^ (k + 1) / Tz k r z' ^ k) * hypMeas k (Tz k r z') f

theorem volU_pos (j : ℕ) : 0 < volU j :=
  Finset.prod_pos fun i _ => by positivity

theorem continuous_pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (pairF k r z z') := by
  unfold pairF herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec
    ((show Continuous fun x : Mt k r => Matrix.of x from continuous_id).matrix_mulVec continuous_const))

theorem gauge_of_lim {k r : ℕ} (νg : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) νg)
    (hL : ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) :
    IsGaugeOn k r (UWb k r) νg := by
  refine ⟨hH, ?_⟩
  have h1 : (1 : Mat k r) ∈ UWb k r := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩⟩ <;> simp [UH]
  have e : ∀ ρ, tBall k r 1 ρ = expBall (k := k) (r := r) (UWb k r) ρ := fun ρ => by
    ext x
    simp [tBall, bBall]
  have h2 := hL 1 h1
  simp only [e] at h2
  exact h2

def annU (T T' : ℝ) : Set ℂ := {ζ | T * T' < Complex.normSq ζ ∧ Complex.normSq ζ < 4 * (T * T')}

theorem annU_open (T T' : ℝ) : IsOpen (annU T T') :=
  (isOpen_lt continuous_const Complex.continuous_normSq).inter
    (isOpen_lt Complex.continuous_normSq continuous_const)

theorem testJ (k : ℕ) (T T' : ℝ) (hTT : 0 < T * T') :
    0 < ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ∧
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ < ⊤ := by
  have hAo : IsOpen (annU T T') := annU_open T T'
  constructor
  ·
    have hVo : IsOpen {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
      (isOpen_lt continuous_const Complex.continuous_normSq).inter
        (isOpen_lt Complex.continuous_normSq continuous_const)
    have hVne : {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.Nonempty := by
      refine ⟨((Real.sqrt (5 / 2 * (T * T')) : ℝ) : ℂ), ?_, ?_⟩ <;>
        rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] <;> linarith
    have hVpos := hVo.measure_pos volume hVne
    have hle : ∀ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
        {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ ≤
        ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')
      · have hU : ζ ∈ annU T T' := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
        have hV : ζ ∈ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        rw [Set.indicator_of_mem hV, Set.indicator_of_mem hU, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos (by linarith [hζ.1])]
        exact pow_le_pow_left₀ hTT.le (by linarith [hζ.1]) _
      · have hV : ζ ∉ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        simp [Set.indicator_apply, hV]
    calc (0 : ℝ≥0∞) < ENNReal.ofReal ((T * T') ^ (k - 1)) *
          volume {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.2 (pow_pos hTT _)).ne' hVpos.ne'
      _ = ∫⁻ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
          {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ := by
          rw [lintegral_const_mul _ (measurable_one.indicator hVo.measurableSet),
            lintegral_indicator_one hVo.measurableSet]
      _ ≤ _ := lintegral_mono hle
  · have hM : ∀ ζ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ≤
        ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : ζ ∈ annU T T'
      · rw [Set.indicator_of_mem hζ, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos hζ.1.le]
        exact pow_le_pow_left₀ (by linarith [hζ.1]) (by linarith [hζ.2]) _
      · simp [Set.indicator_apply, hζ]
    have hsub : annU T T' ⊆ Metric.ball 0 (2 * Real.sqrt (T * T') + 1) := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖ζ‖ ^ 2 < (2 * Real.sqrt (T * T')) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, mul_pow, Real.sq_sqrt hTT.le]
        linarith [hζ.2]
      have h2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
      linarith
    have hfin : volume (annU T T') < ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top
    calc _ ≤ ∫⁻ ζ, ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ :=
          lintegral_mono hM
      _ = ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * volume (annU T T') := by
          rw [lintegral_const_mul _ (measurable_one.indicator hAo.measurableSet),
            lintegral_indicator_one hAo.measurableSet]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem constVal_of (hR : RhsTest) (hP : PairPush) : ConstVal := by
  intro k r z z' μW μW' a a' μsec hW νg c hH hL hrep
  have hg := gauge_of_lim νg hH hL
  have hT := hW.T_pos
  have hT' := hW.T'_pos
  have hTT : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
  have hgm : Measurable ((annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_one.indicator (annU_open _ _).measurableSet
  have hφm : Measurable (fun x => (annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)
      (pairF k r z z' x)) := hgm.comp (continuous_pairF k r z z').measurable
  have h1 := hR k r z z' μW μW' a a' μsec hW _ hgm
  have h2 := hP k r νg hW.k_pos hg z z' hW.z_mem hW.z'_mem hT hT' _ hgm
  have h3 := hrep _ hφm
  obtain ⟨hJ0, hJt⟩ := testJ k (Tz k r z) (Tz k r z') hTT
  rw [h3, h2, ← mul_assoc] at h1

  have h4 := (ENNReal.mul_left_inj hJ0.ne' hJt.ne).1 h1
  have hv := volU_pos k
  have hv1 := volU_pos (k - 1)
  have hpc : 0 < pairConst k (Tz k r z) (Tz k r z') := by
    unfold pairConst
    positivity
  have ha := hW.a_pos
  have ha' := hW.a'_pos
  have h5 := congrArg ENNReal.toReal h4
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpc.le, ENNReal.toReal_ofReal (by positivity)] at h5
  have hc : c.toReal = a * a' / pairConst k (Tz k r z) (Tz k r z') := by
    rw [← h5]
    field_simp
  rw [hc]
  unfold pairConst wbConst
  have hTk : 0 < (Tz k r z * Tz k r z') ^ k := pow_pos hTT k
  field_simp

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.GaugeExists
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def expC (k r : ℕ) : lieE (UWb k r) → Mt k r :=
  fun x i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j

theorem bBall_eq (k r : ℕ) (ρ : ℝ) : bBall k r ρ = expC k r '' Metric.ball 0 ρ := rfl

def HaarDens : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νh : Measure (Mt k r), IsHaarOn (UWb k r) νh ∧
    ∃ δ : lieE (UWb k r) → ℝ≥0∞, ContinuousAt δ 0 ∧ δ 0 ≠ 0 ∧ δ 0 ≠ ⊤ ∧
      ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → νh (bBall k r ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x

namespace GE

variable {k r : ℕ}

def p0 (k r : ℕ) : Fin (2 * r + k + 1) := wI k r 0

theorem firstMiddle_val : (p0 k r).val = r := by
  show r + (0 : Fin (k + 1)).val = r
  simp

theorem splitHermForm_firstMiddle_apply (j : Fin (2 * r + k + 1)) (hj : j ≠ p0 k r) : Hpk k r (p0 k r) j = 0 := by
  have hv := firstMiddle_val (k := k) (r := r)
  simp only [Hpk]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | (exfalso; omega)

theorem splitHermForm_apply_firstMiddle (i : Fin (2 * r + k + 1)) (hi : i ≠ p0 k r) : Hpk k r i (p0 k r) = 0 := by
  have hv := firstMiddle_val (k := k) (r := r)
  simp only [Hpk]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | (exfalso; omega)

def dg (k r : ℕ) (u : ℂ) : Mat k r := diagonal fun i => if i = p0 k r then u else 1

theorem dg_uh (u : ℂ) (hu : star u * u = 1) : dg k r u ∈ UH (Hpk k r) := by
  show (dg k r u)ᴴ * Hpk k r * dg k r u = Hpk k r
  unfold dg
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul]
  by_cases hi : i = p0 k r <;> by_cases hj : j = p0 k r
  · subst hi
    subst hj
    simp only [Pi.star_apply, if_true]
    linear_combination (Hpk k r (p0 k r) (p0 k r)) * hu
  · subst hi
    simp only [Pi.star_apply, if_true, if_neg hj, splitHermForm_firstMiddle_apply j hj, mul_zero, zero_mul]
  · subst hj
    simp only [Pi.star_apply, if_true, if_neg hi, splitHermForm_apply_firstMiddle i hi, mul_zero, zero_mul]
  · simp only [Pi.star_apply, if_neg hi, if_neg hj, star_one, one_mul, mul_one]

theorem dg_fix (u : ℂ) (e : Fin (2 * r + k + 1)) (he : e ≠ p0 k r) : dg k r u *ᵥ bvec e = bvec e := by
  funext x
  unfold dg
  rw [Matrix.mulVec_diagonal]
  by_cases hx : x = e
  · subst hx
    simp [he]
  · simp [bvec, hx]

theorem dg_mem (u : ℂ) (hu : star u * u = 1) : dg k r u ∈ UWb k r := by
  show dg k r u ∈ UH (Hpk k r) ∧ ∀ a : Fin r, dg k r u *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
    dg k r u *ᵥ bvec (esI k r a) = bvec (esI k r a)
  have hv := firstMiddle_val (k := k) (r := r)
  refine ⟨dg_uh u hu, fun a => ⟨dg_fix u _ ?_, dg_fix u _ ?_⟩⟩
  · intro h
    have h1 : (eI k r a).val = (p0 k r).val := congrArg Fin.val h
    have h2 : (eI k r a).val = a.val := rfl
    have h3 := a.isLt
    omega
  · intro h
    have h1 : (esI k r a).val = (p0 k r).val := congrArg Fin.val h
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    have h3 := a.isLt
    omega

def dV (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := fun i => if i = p0 k r then Complex.I else 0

theorem exp_dV (t : ℝ) : NormedSpace.exp ((t : ℂ) • diagonal (dV k r)) = dg k r (Complex.exp (t * Complex.I)) := by
  unfold dg
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  simp only [Pi.smul_apply, dV]
  split_ifs
  · rw [Complex.exp_eq_exp_ℂ, smul_eq_mul]
  · simp

theorem unit_exp (t : ℝ) : star (Complex.exp (t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem lie_nontrivial : Nontrivial (lieE (UWb k r)) := by
  rw [Submodule.nontrivial_iff_ne_bot, Submodule.ne_bot_iff]
  refine ⟨(WithLp.equiv 2 _).symm (realifyFun (diagonal (dV k r))), Submodule.subset_span
    ⟨diagonal (dV k r), (show diagonal (dV k r) ∈ lieOf (UWb k r) from fun t => by
      rw [exp_dV]
      exact dg_mem _ (unit_exp t)), rfl⟩, ?_⟩
  intro h
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) =>
    x (p0 k r, p0 k r, true)) h
  simp [realifyFun, dV] at h1

theorem haarOn_smul (S : Set (Mat k r)) (ν : Measure (Mt k r)) (c : ℝ≥0) (hc : c ≠ 0) (h : IsHaarOn S ν) :
    IsHaarOn S (c • ν) := by
  refine ⟨?_, ?_, ?_, fun s hs => ?_⟩
  · have := h.1
    infer_instance
  · intro h0
    apply h.2.1
    rw [← Measure.measure_univ_eq_zero]
    have h1 := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simpa [hc] using h1
  · rw [Measure.smul_apply, h.2.2.1, smul_zero]
  · rw [Measure.map_smul, h.2.2.2 s hs]
    exact (HU.lmulM_cont s).measurable.aemeasurable

theorem tBall_mass (ν : Measure (Mt k r)) (h : IsHaarOn (UWb k r) ν) (m : Mat k r) (hm : m ∈ UWb k r) (ρ : ℝ) :
    ν (tBall k r m ρ) = ν (bBall k r ρ) := by
  have hinv := HU.uwb_inv hm
  have hB : MeasurableSet (bBall k r ρ) := measurableSet_expBall k r (UWb k r) ρ
  calc ν (tBall k r m ρ) = ν (lmulM m⁻¹ ⁻¹' bBall k r ρ) := rfl
    _ = (ν.map (lmulM m⁻¹)) (bBall k r ρ) := (Measure.map_apply (HU.lmulM_cont _).measurable hB).symm
    _ = ν (bBall k r ρ) := by rw [h.2.2.2 _ hinv]

end GE


open GE in
theorem gaugeExists_of (hH : HaarDens) (hL : ChartLim) : GaugeExists := by
  intro k r hk
  obtain ⟨νh, hνh, δ, hδc, hδ0, hδt, ε, hε, hball⟩ := hH k r hk
  set c : ℝ≥0 := ((δ 0).toNNReal)⁻¹ with hcdef
  have hc : c ≠ 0 := inv_ne_zero (ENNReal.toNNReal_pos hδ0 hδt).ne'
  have hg : IsHaarOn (UWb k r) (c • νh) := haarOn_smul _ _ c hc hνh
  have hup : ∀ᶠ x in 𝓝 (0 : lieE (UWb k r)), δ x < δ 0 + 1 :=
    hδc.eventually (gt_mem_nhds (ENNReal.lt_add_right hδt one_ne_zero))
  have hlo : ∀ᶠ x in 𝓝 (0 : lieE (UWb k r)), δ 0 / 2 < δ x :=
    hδc.eventually (lt_mem_nhds (ENNReal.half_lt_self hδ0 hδt))
  obtain ⟨ε', hε', hε'b⟩ := Metric.eventually_nhds_iff.mp (hup.and hlo)
  refine ⟨c • νh, hg, ⟨min ε ε', lt_min hε hε', fun ρ hρ hρε => ?_⟩, fun m hm => ?_⟩
  · have hρ1 : ρ < ε := hρε.trans_le (min_le_left _ _)
    have hρ2 : ρ < ε' := hρε.trans_le (min_le_right _ _)
    have hbd : ∀ x ∈ Metric.ball (0 : lieE (UWb k r)) ρ, δ x < δ 0 + 1 ∧ δ 0 / 2 < δ x :=
      fun x hx => hε'b ((Metric.mem_ball.mp hx).trans hρ2)
    have hmeas : MeasurableSet (Metric.ball (0 : lieE (UWb k r)) ρ) := measurableSet_ball
    have hvpos : 0 < volume (Metric.ball (0 : lieE (UWb k r)) ρ) := Metric.measure_ball_pos _ _ hρ
    have hvfin : volume (Metric.ball (0 : lieE (UWb k r)) ρ) < ⊤ := measure_ball_lt_top
    have hI : νh (bBall k r ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x := hball ρ hρ hρ1
    have hlow : δ 0 / 2 * volume (Metric.ball (0 : lieE (UWb k r)) ρ) ≤ νh (bBall k r ρ) := by
      rw [hI, ← setLIntegral_const]
      exact setLIntegral_mono' hmeas fun x hx => (hbd x hx).2.le
    have hhigh : νh (bBall k r ρ) ≤ (δ 0 + 1) * volume (Metric.ball (0 : lieE (UWb k r)) ρ) := by
      rw [hI, ← setLIntegral_const]
      exact setLIntegral_mono' hmeas fun x hx => (hbd x hx).1.le
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    constructor
    · exact ENNReal.mul_pos (by exact_mod_cast hc)
        (lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.half_pos hδ0).ne' hvpos.ne') hlow).ne'
    · exact ENNReal.mul_lt_top ENNReal.coe_lt_top
        (lt_of_le_of_lt hhigh (ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨hδt.lt_top, ENNReal.one_lt_top⟩) hvfin))
  · have := lie_nontrivial (k := k) (r := r)
    have hlim := hL (lieE (UWb k r)) (Mt k r) (expC k r) νh δ hδc hδt
      ⟨ε, hε, fun ρ h1 h2 => by rw [← bBall_eq]; exact hball ρ h1 h2⟩
    have key : (fun ρ : ℝ => ((c • νh) (tBall k r m ρ)).toReal / bVol k r ρ) = fun ρ => (c : ℝ) *
        ((νh (expC k r '' Metric.ball 0 ρ)).toReal / (volume (Metric.ball (0 : lieE (UWb k r)) ρ)).toReal) := by
      funext ρ
      rw [tBall_mass _ hg m hm ρ, Measure.smul_apply, ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul, bBall_eq,
        bVol, mul_div_assoc]
    have h1 : (c : ℝ) * (δ 0).toReal = 1 := by
      rw [hcdef, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]
      exact inv_mul_cancel₀ (ENNReal.toReal_pos hδ0 hδt).ne'
    rw [key]
    have h2 := hlim.const_mul (c : ℝ)
    rwa [h1] at h2

theorem gaugeExists_of_dens (hH : HaarDens) : GaugeExists := gaugeExists_of hH chartLim

end PI.RhsWLim.W
end
end

