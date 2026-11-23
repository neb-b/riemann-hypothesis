module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtWeakA
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff

noncomputable def extCh (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem extCh_contDiff : ContDiff ℝ ∞ extCh :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem extCh_nonneg (t : ℝ) : 0 ≤ extCh t := Real.smoothTransition.nonneg _

theorem extCh_le_one (t : ℝ) : extCh t ≤ 1 := Real.smoothTransition.le_one _

theorem extCh_of_le_one {t : ℝ} (ht : t ≤ 1) : extCh t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem extCh_of_two_le {t : ℝ} (ht : 2 ≤ t) : extCh t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem deriv_extCh_of_lt_one {t : ℝ} (ht : t < 1) : deriv extCh t = 0 := by
  have h : extCh =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact extCh_of_le_one (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem deriv_extCh_of_two_lt {t : ℝ} (ht : 2 < t) : deriv extCh t = 0 := by
  have h : extCh =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact extCh_of_two_le (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem exists_deriv_extCh_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖deriv extCh t‖ ≤ C := by
  have hc : Continuous (deriv extCh) := extCh_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv extCh) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro t ht
    rcases lt_or_ge t 1 with h1 | h1
    · exact deriv_extCh_of_lt_one h1
    · have h2 : 2 < t := by
        by_contra h2
        exact ht ⟨h1, not_lt.1 h2⟩
      exact deriv_extCh_of_two_lt h2
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

variable {n : ℕ}

noncomputable def extCut (F : V n → ℂ) (k : ℝ) (z : V n) : ℝ :=
  if F z = 0 then 0 else extCh (-Real.log (‖F z‖ ^ 2) / k)

theorem logCutoff_nonneg (F : V n → ℂ) (k : ℝ) (z : V n) : 0 ≤ extCut F k z := by
  unfold extCut
  split_ifs
  · exact le_rfl
  · exact extCh_nonneg _

theorem logCutoff_le_one (F : V n → ℂ) (k : ℝ) (z : V n) : extCut F k z ≤ 1 := by
  unfold extCut
  split_ifs
  · exact zero_le_one
  · exact extCh_le_one _

theorem logCutoff_eq_one {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n} (hz : F z ≠ 0)
    (h : -Real.log (‖F z‖ ^ 2) ≤ k) : extCut F k z = 1 := by
  simp only [extCut, hz, if_false]
  exact extCh_of_le_one ((div_le_one hk).2 h)

theorem logCutoff_eventuallyEq_zero {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hFc : ContinuousAt F z) (hz : F z = 0) : extCut F k =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have hball : Metric.ball (0 : ℂ) (Real.exp (-k)) ∈ 𝓝 (F z) := by
    rw [hz]
    exact Metric.ball_mem_nhds _ (Real.exp_pos _)
  filter_upwards [hFc.preimage_mem_nhds hball] with w hw
  have hw' : ‖F w‖ < Real.exp (-k) := by simpa using hw
  unfold extCut
  split_ifs with h0
  · rfl
  · apply extCh_of_two_le
    have hpos : 0 < ‖F w‖ := norm_pos_iff.2 h0
    have hlog : Real.log ‖F w‖ < -k := by
      have := Real.log_lt_log hpos hw'
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hk, Real.log_pow]
    push_cast
    linarith

theorem contDiffAt_logCutoff {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : ContDiffAt ℝ ∞ F z) : ContDiffAt ℝ ∞ (extCut F k) z := by
  by_cases h0 : F z = 0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (logCutoff_eventuallyEq_zero hk hF.continuousAt h0)
  · have hin : ContDiffAt ℝ ∞ (fun w => -Real.log (‖F w‖ ^ 2) / k) z := by
      have h2 : ContDiffAt ℝ ∞ (fun w => ‖F w‖ ^ 2) z := hF.norm_sq ℝ
      have hne : ‖F z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h0)
      exact ((h2.log hne).neg).div_const k
    have hcomp : ContDiffAt ℝ ∞ (fun w => extCh (-Real.log (‖F w‖ ^ 2) / k)) z :=
      extCh_contDiff.contDiffAt.comp z hin
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hF.continuousAt.eventually_ne h0] with w hw
    simp [extCut, hw]

theorem isTest_logCutoff_mul {Ω : Set (V n)} {F : V n → ℂ}
    (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z) {k : ℝ} (hk : 0 < k) {g : V n → ℂ} (hg : IsTest Ω g) :
    IsTest (Ω \ {z | F z = 0}) (fun z => (extCut F k z : ℂ) * g z) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport g
    · have hzΩ : z ∈ Ω := hg.2.2 hz
      have hc : ContDiffAt ℝ ∞ (fun w => (extCut F k w : ℂ)) z :=
        ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_logCutoff hk (hsm z hzΩ))
      exact hc.mul (hg.1.contDiffAt)
    · have hg0 : g =ᶠ[𝓝 z] 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
      refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ => (0 : ℂ)) z).congr_of_eventuallyEq ?_
      filter_upwards [hg0] with w hw
      simp [hw]
  · exact hg.2.1.mul_left
  · intro z hz
    have hzg : z ∈ tsupport g := tsupport_mul_subset_right hz
    have hzΩ : z ∈ Ω := hg.2.2 hzg
    refine ⟨hzΩ, ?_⟩
    intro hF0
    have hF0' : F z = 0 := hF0
    have hcut := logCutoff_eventuallyEq_zero hk (hsm z hzΩ).continuousAt hF0'
    have hprod : (fun w => (extCut F k w : ℂ) * g w) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hcut] with w hw
      simp [hw]
    exact ((notMem_tsupport_iff_eventuallyEq).2 hprod) hz

theorem fderiv_logCutoff {F : V n → ℂ} {k : ℝ} {z : V n}
    (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    fderiv ℝ (extCut F k) z = deriv extCh (-Real.log (‖F z‖ ^ 2) / k) •
      ((-k⁻¹) • fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) := by
  have hne : ‖F z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hz)
  have hL : HasFDerivAt (fun w => Real.log (‖F w‖ ^ 2))
      (fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) z :=
    (((hF.norm_sq ℝ).log hne)).hasFDerivAt
  have e : (fun w => -Real.log (‖F w‖ ^ 2) / k) =
      fun w => (-k⁻¹) • Real.log (‖F w‖ ^ 2) := by
    funext w
    simp only [smul_eq_mul]
    ring
  have hh : HasFDerivAt (fun w => -Real.log (‖F w‖ ^ 2) / k)
      ((-k⁻¹) • fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) z := by
    rw [e]
    exact hL.const_smul (-k⁻¹ : ℝ)
  have hd : HasDerivAt extCh (deriv extCh (-Real.log (‖F z‖ ^ 2) / k))
      (-Real.log (‖F z‖ ^ 2) / k) :=
    ((extCh_contDiff.differentiable (by simp)) _).hasDerivAt
  have hcomp := hd.comp_hasFDerivAt z hh
  have heq : extCut F k =ᶠ[𝓝 z] extCh ∘ fun w => -Real.log (‖F w‖ ^ 2) / k := by
    filter_upwards [hF.continuousAt.eventually_ne hz] with w hw
    simp [extCut, hw]
  rw [heq.fderiv_eq]
  exact hcomp.fderiv

theorem norm_fderiv_logCutoff_le {F : V n → ℂ} {k C : ℝ} (hk : 0 < k)
    (hC : ∀ t, ‖deriv extCh t‖ ≤ C) {z : V n} (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    ‖fderiv ℝ (extCut F k) z‖ ≤ C * k⁻¹ * ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ := by
  rw [fderiv_logCutoff hF hz, norm_smul, norm_smul, norm_neg, norm_inv,
    Real.norm_of_nonneg hk.le, ← mul_assoc]
  gcongr
  exact hC _

theorem fderiv_logCutoff_eq_zero {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0)
    (h : ¬ (k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k)) :
    fderiv ℝ (extCut F k) z = 0 := by
  rw [fderiv_logCutoff hF hz]
  set a := -Real.log (‖F z‖ ^ 2) with ha
  have hd : deriv extCh (a / k) = 0 := by
    by_cases h1 : k ≤ a
    · have h2 : 2 * k < a := by
        push_neg at h
        exact h h1
      exact deriv_extCh_of_two_lt ((lt_div_iff₀ hk).2 (by linarith))
    · push_neg at h1
      exact deriv_extCh_of_lt_one ((div_lt_one hk).2 h1)
  rw [hd, zero_smul]

theorem dbarDir_extensionCutoff_mul {F g : V n → ℂ} {k : ℝ} {z : V n} (v : V n)
    (hc : DifferentiableAt ℝ (extCut F k) z) (hg : DifferentiableAt ℝ g z) :
    dbarDir (fun w => (extCut F k w : ℂ) * g w) z v =
      (extCut F k z : ℂ) * dbarDir g z v + g z * ((fderiv ℝ (extCut F k) z (I • v) : ℂ) -
        I * (fderiv ℝ (extCut F k) z v : ℂ)) := by
  have hcC : HasFDerivAt (fun w => (extCut F k w : ℂ))
      (ofRealCLM.comp (fderiv ℝ (extCut F k) z)) z :=
    ofRealCLM.hasFDerivAt.comp z hc.hasFDerivAt
  unfold dbarDir
  have hm : HasFDerivAt (fun w => (extCut F k w : ℂ) * g w)
      ((extCut F k z : ℂ) • fderiv ℝ g z + g z • (ofRealCLM.comp (fderiv ℝ (extCut F k) z))) z :=
    hcC.mul hg.hasFDerivAt
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ofRealCLM_apply]
  ring

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralBumpProfOnePos
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

variable {n : ℕ}

noncomputable def bumpProf (t s : ℝ) : ℝ := Real.smoothTransition (1 - 4 * (s / t) ^ 2)

noncomputable def mollConst (n : ℕ) : ℝ := (∫ z : V n, bumpProf 1 ‖z‖)⁻¹

noncomputable def mollProf (n : ℕ) (t s : ℝ) : ℝ := mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t s

noncomputable def moll (n : ℕ) (t : ℝ) (z : V n) : ℝ := mollProf n t ‖z‖

noncomputable def mollify (n : ℕ) (t : ℝ) (u : V n → ℂ) (x : V n) : ℂ :=
  ∫ y, (moll n t (x - y) : ℂ) * u y

theorem finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

theorem bumpProf_scale {t : ℝ} (ht : 0 < t) (z : V n) : bumpProf t ‖z‖ = bumpProf 1 ‖t⁻¹ • z‖ := by
  simp only [bumpProf, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, div_one]
  congr 1
  ring

theorem integral_bumpProf {t : ℝ} (ht : 0 < t) :
    ∫ z : V n, bumpProf t ‖z‖ = t ^ (2 * n) * ∫ z : V n, bumpProf 1 ‖z‖ := by
  simp_rw [bumpProf_scale ht]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z : V n => bumpProf 1 ‖z‖) ht.le,
    finrank_V, smul_eq_mul]

private lemma bumpProf_eq_zero_of_half_lt {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) : bumpProf t s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 1 / 2 < s / t := by rw [lt_div_iff₀ ht]; linarith
  nlinarith

private lemma continuous_bumpProf_norm (n : ℕ) (t : ℝ) : Continuous (fun z : V n => bumpProf t ‖z‖) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

theorem integral_bumpProf_one_pos (n : ℕ) : 0 < ∫ z : V n, bumpProf 1 ‖z‖ := by
  have hcs : HasCompactSupport (fun z : V n => bumpProf 1 ‖z‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V n) (1 / 2)) fun z hz => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact bumpProf_eq_zero_of_half_lt one_pos hz
  refine (continuous_bumpProf_norm n 1).integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun z => Real.smoothTransition.nonneg _) (x := 0) ?_
  simp [bumpProf]

theorem mollConst_nonneg (n : ℕ) : 0 ≤ mollConst n := by
  unfold mollConst
  exact inv_nonneg.mpr (integral_nonneg fun z => Real.smoothTransition.nonneg _)

theorem moll_nonneg (n : ℕ) (t : ℝ) (z : V n) : 0 ≤ moll n t z := by
  have h : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
  exact mul_nonneg (mul_nonneg (mollConst_nonneg n) (inv_nonneg.mpr h)) (Real.smoothTransition.nonneg _)

theorem moll_contDiff (n : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (moll n t) := by
  have h : moll n t = fun z => mollConst n * (t ^ (2 * n))⁻¹ *
      Real.smoothTransition (1 - 4 * (‖z‖ ^ 2 / t ^ 2)) := by
    funext z
    simp only [moll, mollProf, bumpProf, div_pow]
  rw [h]
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul ((contDiff_norm_sq ℂ).div_const _))))

theorem moll_tsupport (n : ℕ) {t : ℝ} (ht : 0 < t) : tsupport (moll n t) ⊆ closedBall 0 (t / 2) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra hnot
  rw [mem_closedBall, dist_zero_right, not_le] at hnot
  apply hz
  simp only [moll, mollProf, bumpProf_eq_zero_of_half_lt ht hnot, mul_zero]

theorem moll_hasCompactSupport (n : ℕ) {t : ℝ} (ht : 0 < t) : HasCompactSupport (moll n t) := by
  exact (isCompact_closedBall (0 : V n) (t / 2)).of_isClosed_subset (isClosed_tsupport _)
    (moll_tsupport n ht)

theorem moll_integral (n : ℕ) {t : ℝ} (ht : 0 < t) : ∫ z : V n, moll n t z = 1 := by
  simp only [moll, mollProf]
  rw [integral_const_mul, integral_bumpProf ht, mollConst]
  have h1 := integral_bumpProf_one_pos n
  have h2 : t ^ (2 * n) ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp

theorem moll_le (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ z : V n, moll n t z ≤ C / volume.real (ball (0 : V n) t) := by
  refine ⟨mollConst n * volume.real (ball (0 : V n) 1), fun t ht z => ?_⟩
  have hv : 0 < volume.real (ball (0 : V n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : V n) one_pos).ne' measure_ball_lt_top.ne
  have hball : volume.real (ball (0 : V n) t) = t ^ (2 * n) * volume.real (ball (0 : V n) 1) := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume (0 : V n) ht, finrank_V,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos ht _).le]
  rw [hball, mul_div_mul_right _ _ hv.ne']
  have htp : 0 < t ^ (2 * n) := pow_pos ht _
  have hb : bumpProf t ‖z‖ ≤ 1 := Real.smoothTransition.le_one _
  have hc := mollConst_nonneg n
  simp only [moll, mollProf]
  calc mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t ‖z‖
      ≤ mollConst n * (t ^ (2 * n))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hc (inv_nonneg.mpr htp.le))
    _ = mollConst n / t ^ (2 * n) := by ring

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MvDivIntegrand
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem finrank_real_V {n : ℕ} : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace_fin]

theorem mvPow : MVPowStatement := by
  intro n s hn
  haveI : Nontrivial (V n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_V]; omega)
  have hind : (ball (0 : V n) 1).indicator (fun z : V n => ‖z‖ ^ (-2 * s)) =
      fun z => (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ < 1 <;> simp [Set.indicator, mem_ball_zero_iff, h]
  rw [← integrable_indicator_iff measurableSet_ball, hind, integrable_fun_norm_addHaar,
    finrank_real_V]
  have hfun : (fun y : ℝ => y ^ (2 * n - 1) • (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) y) =
      (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s)) := by
    funext y
    simp only [indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio, ← IntegrableOn]
  have hcongr : EqOn (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s))
      (fun y : ℝ => y ^ ((2 * n : ℝ) - 1 - 2 * s)) (Ioo 0 1) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  rw [integrableOn_congr_fun hcongr measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

theorem mvDiv : MVDivStatement := by
  intro n hn
  have hpow := mvPow n n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℕ → V n → ℝ≥0∞ := fun k z => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))
    with hf
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    (by fun_prop : Measurable fun z : V n => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ))))
  have hmono : Monotone f := by
    intro k m hkm z
    show ENNReal.ofReal _ ≤ ENNReal.ofReal _
    apply ENNReal.ofReal_le_ofReal
    have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
    apply Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)) _
      (neg_nonpos.mpr (Nat.cast_nonneg _))
    gcongr
  have hinf : ∫⁻ z in ball (0 : V n) 1, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) = ∞ := by
    by_contra h
    have hlt := lt_top_iff_ne_top.mpr h
    have hint : IntegrableOn (fun z : V n => ‖z‖ ^ (-2 * (n : ℝ))) (ball 0 1) := by
      refine ⟨(measurable_norm.pow_const _).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal ?_).mpr hlt⟩
      exact ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) _
    exact lt_irrefl _ (hpow.mp hint)
  have hsup : ∀ z : V n, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ ⨆ k, f k z := by
    intro z
    by_cases hz : z = 0
    · subst hz
      rw [norm_zero, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
      exact zero_le
    · have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have h1 : Tendsto (fun k : ℕ => ‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖z‖ ^ 2 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h1.rpow_const (p := -(n : ℝ)) (Or.inl (by positivity))
      have ht : Tendsto (fun k : ℕ => f k z) atTop (𝓝 (ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))))) := by
        show Tendsto (fun k : ℕ => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))) atTop _
        apply ENNReal.tendsto_ofReal
        convert h2 using 2
        rw [add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
        congr 1
        push_cast
        ring
      exact le_of_tendsto' ht (fun k => le_iSup (fun k => f k z) k)
  have hbig : ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z = ∞ := by
    rw [← lintegral_iSup hmeas hmono]
    refine top_le_iff.mp ?_
    rw [← hinf]
    exact lintegral_mono hsup
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  have hM : (M : ℝ≥0∞) < ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z := by
    rw [hbig]
    exact ENNReal.coe_lt_top
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hM
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with δ hδ
  refine hk.trans_le (lintegral_mono fun z => ?_)
  show ENNReal.ofReal _ ≤ ENNReal.ofReal _
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ.1)
    (by linarith [hδ.2]) (neg_nonpos.mpr (Nat.cast_nonneg _))

end ReciprocityTheory.L2DbarEstimates.C
end

