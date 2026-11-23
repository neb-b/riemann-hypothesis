module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Circle
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem measurePreserving_smul_unit {n : ℕ} (a : ℂ) (ha : ‖a‖ = 1) :
    MeasurePreserving (fun z : V n => a • z) volume volume := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let L : V n ≃ₗᵢ[ℝ] V n :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ (V n) a ha0).restrictScalars ℝ
      norm_map' := fun z => by simp [norm_smul, ha] }
  have hL : (fun z : V n => a • z) = L := by
    funext z
    rfl
  rw [hL]
  exact L.measurePreserving

theorem circle_mean {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (c + Complex.exp ((θ : ℂ) * I) • w) =
      ((2 * Real.pi : ℝ) : ℂ) * u c := by
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hρ1 : 1 < R / ‖w‖ := by
    rw [lt_div_iff₀ hwpos]
    linarith
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.ball 0 (R / ‖w‖)) := by
    intro ζ hζ
    have hmem : c + ζ • w ∈ ball c R := by
      rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hwpos] at hζ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact hζ
    have h1 : DifferentiableAt ℂ u (c + ζ • w) := hu.differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => c + ζ • w) ζ :=
      (differentiableAt_id.smul_const w).const_add c
    exact (h1.comp ζ h2).differentiableWithinAt
  have hcl : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.closedBall 0 1) :=
    hg.mono (Metric.closedBall_subset_ball hρ1)
  have key := hcl.circleIntegral_sub_inv_smul (w := 0) (by simp)
  simp only [circleIntegral, deriv_circleMap, sub_zero, smul_eq_mul, zero_smul, add_zero] at key
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp ((θ : ℂ) * I) := by
    intro θ
    simp [circleMap]
  have h3 : ∀ θ : ℝ, circleMap 0 1 θ * I * ((circleMap 0 1 θ)⁻¹ * u (c + circleMap 0 1 θ • w)) =
      I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by
    intro θ
    have hne : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
    rw [hcm θ] at hne ⊢
    calc Complex.exp ((θ : ℂ) * I) * I * ((Complex.exp ((θ : ℂ) * I))⁻¹ * u (c + Complex.exp ((θ : ℂ) * I) • w))
        = I * u (c + Complex.exp ((θ : ℂ) * I) • w) * (Complex.exp ((θ : ℂ) * I) * (Complex.exp ((θ : ℂ) * I))⁻¹) := by ring
      _ = I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by rw [mul_inv_cancel₀ hne, mul_one]
  simp only [h3, intervalIntegral.integral_const_mul] at key
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [key]
  push_cast
  ring

theorem circle_mean_sq {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖u (c + Complex.exp ((θ : ℂ) * I) • w)‖ₑ ^ 2 := by
  have hmem : ∀ θ : ℝ, c + Complex.exp ((θ : ℂ) * I) • w ∈ ball c R := by
    intro θ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hw
  set F : ℝ → ℂ := fun θ => u (c + Complex.exp ((θ : ℂ) * I) • w) with hF
  have hcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    have h1 := (hu.differentiableAt (isOpen_ball.mem_nhds (hmem θ))).continuousAt
    have h2 : Continuous fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w := by fun_prop
    show ContinuousAt (u ∘ fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) θ
    exact ContinuousAt.comp (f := fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) (x := θ) h1
      h2.continuousAt
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hI : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ = ((2 * Real.pi : ℝ) : ℂ) * u c := by
    rw [← intervalIntegral.integral_of_le hpi]
    exact circle_mean hu hw
  have hint : IntegrableOn F (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun θ => ‖F θ‖ ^ 2) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    ((hcont.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcr : Continuous fun θ => (F θ * (starRingEnd ℂ) (u c)).re :=
    Complex.continuous_re.comp (hcont.mul continuous_const)
  have hint3 : IntegrableOn (fun θ => (F θ * (starRingEnd ℂ) (u c)).re) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcr.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpt : ∀ θ, 2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2 ≤ ‖F θ‖ ^ 2 := by
    intro θ
    have h := Complex.normSq_nonneg (F θ - u c)
    rw [Complex.normSq_sub] at h
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  have hre : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
      2 * Real.pi * ‖u c‖ ^ 2 := by
    have h1 : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
        (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ * (starRingEnd ℂ) (u c)).re :=
      integral_re (hint.mul_const _)
    rw [h1, integral_mul_const, hI, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hreal : ‖u c‖ ^ 2 * (2 * Real.pi) ≤ ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 := by
    have h : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2) ≤
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 :=
      integral_mono ((hint3.const_mul 2).sub (integrable_const (‖u c‖ ^ 2))) hint2 hpt
    rw [integral_sub (hint3.const_mul 2) (integrable_const _), integral_const_mul, hre,
      integral_const] at h
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, smul_eq_mul] at h
    have hv : (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real univ = 2 * Real.pi := by
      simp [Measure.real, Real.volume_Ioc, hpi, Real.pi_pos.le]
    rw [hv] at h
    linarith
  have hen : ∀ θ, ‖F θ‖ₑ ^ 2 = ENNReal.ofReal (‖F θ‖ ^ 2) := fun θ => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  show ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ₑ ^ 2
  simp_rw [hen]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun θ => by positivity),
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCutA
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable section

def cutL (ε s : ℝ) : ℝ := Real.log (s + ε) - Real.log ε

def cutP (ε s : ℝ) : ℝ := cutL ε s ^ 2 / 2

def halfLogRatioSqDeriv (ε s : ℝ) : ℝ := cutL ε s / (s + ε)

def halfLogRatioSqSecondDeriv (ε s : ℝ) : ℝ := (1 - cutL ε s) / (s + ε) ^ 2

lemma hasDerivAt_cutL {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutL ε) (s + ε)⁻¹ s := by
  have h1 := (((hasDerivAt_id s).add_const ε).log h.ne').sub_const (Real.log ε)
  show HasDerivAt (fun s => Real.log (s + ε) - Real.log ε) _ s
  simpa [one_div] using h1

lemma hasDerivAt_cutP {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutP ε) (halfLogRatioSqDeriv ε s) s := by
  have h1 := ((hasDerivAt_cutL h).pow 2).div_const 2
  show HasDerivAt (fun s => cutL ε s ^ 2 / 2) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqDeriv
  field_simp
  ring

lemma hasDerivAt_halfLogRatioSqDeriv {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (halfLogRatioSqDeriv ε) (halfLogRatioSqSecondDeriv ε s) s := by
  have h1 := (hasDerivAt_cutL h).div ((hasDerivAt_id s).add_const ε) h.ne'
  show HasDerivAt (fun s => cutL ε s / (s + ε)) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqSecondDeriv
  simp only [id]
  field_simp

lemma cutL_nonneg {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ cutL ε s := by
  unfold cutL
  exact sub_nonneg.2 (Real.log_le_log hε (by linarith))

lemma cutL_mono {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutL ε s ≤ cutL ε t := by
  unfold cutL
  exact sub_le_sub_right (Real.log_le_log (by linarith) (by linarith)) _

lemma polydiscCutoff_nonneg (ε s : ℝ) : 0 ≤ cutP ε s := by
  unfold cutP
  positivity

lemma cutP_mono {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutP ε s ≤ cutP ε t := by
  unfold cutP
  nlinarith [cutL_nonneg hε hs, cutL_mono hε hs hst]

lemma cut_rho_eq {ε s : ℝ} (h : 0 < s + ε) :
    s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s = (s + ε * cutL ε s) / (s + ε) ^ 2 := by
  unfold halfLogRatioSqSecondDeriv halfLogRatioSqDeriv
  field_simp
  ring

lemma cut_rho_nonneg {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s := by
  rw [cut_rho_eq (by linarith)]
  exact div_nonneg (add_nonneg hs (mul_nonneg hε.le (cutL_nonneg hε hs))) (by positivity)

lemma cut_rho_ge {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) :
    s⁻¹ ≤ 4 * (s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s) := by
  have hs0 : 0 < s := lt_of_lt_of_le hε hs
  have hL := cutL_nonneg hε hs0.le
  rw [cut_rho_eq (by linarith), inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hs0 (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ 3 * s + ε),
    mul_nonneg hs0.le (mul_nonneg hε.le hL)]

lemma cutP_le {k m : ℝ} (hk : 1 ≤ k) (hm : 0 ≤ m) :
    cutP (Real.exp (-2 * k)) m ≤ (m + 2) ^ 2 / 2 * k ^ 2 := by
  have hε : 0 < Real.exp (-2 * k) := Real.exp_pos _
  have hε1 : Real.exp (-2 * k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hLe : cutL (Real.exp (-2 * k)) m = Real.log (m + Real.exp (-2 * k)) + 2 * k := by
    unfold cutL
    rw [Real.log_exp]
    ring
  have hlog : Real.log (m + Real.exp (-2 * k)) ≤ m + Real.exp (-2 * k) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hL0 := cutL_nonneg hε hm
  have hLup : cutL (Real.exp (-2 * k)) m ≤ (m + 2) * k := by
    rw [hLe]
    nlinarith
  unfold cutP
  nlinarith [mul_le_mul hLup hLup hL0 (by positivity : (0 : ℝ) ≤ (m + 2) * k)]

lemma continuousAt_cutP {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (cutP ε) s :=
  (hasDerivAt_cutP h).continuousAt

lemma continuousAt_halfLogRatioSqDeriv {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqDeriv ε) s :=
  (hasDerivAt_halfLogRatioSqDeriv h).continuousAt

lemma continuousAt_halfLogRatioSqSecondDeriv {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqSecondDeriv ε) s := by
  show ContinuousAt (fun s => (1 - cutL ε s) / (s + ε) ^ 2) s
  exact (continuousAt_const.sub (hasDerivAt_cutL h).continuousAt).div (by fun_prop)
    (pow_ne_zero 2 h.ne')

variable {n : ℕ}

def complexLineSecondDeriv (F : V n → ℂ) (z e : V n) : ℂ := deriv (deriv (fun l : ℂ => F (z + l • e))) 0

lemma real_smul_smul (t : ℝ) (μ : ℂ) (e : V n) : t • (μ • e) = ((t : ℂ) * μ) • e := by
  rw [← Complex.coe_smul, smul_smul]

lemma deriv_slice {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} {l : ℂ} (hw : z + l • e ∈ Ω) :
    deriv (fun m : ℂ => F (z + m • e)) l = fderiv ℂ F (z + l • e) e := by
  have hd : DifferentiableAt ℂ F (z + l • e) := hF.differentiableAt (hΩ.mem_nhds hw)
  have hl : HasDerivAt (fun m : ℂ => z + m • e) e l := by
    simpa using ((hasDerivAt_id l).smul_const e).const_add z
  exact (hd.hasFDerivAt.comp_hasDerivAt l hl).deriv

lemma hasDerivAt_line {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => F (z + t • (μ • e))) (fderiv ℂ F z e * μ) 0 := by
  have hd : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hl : HasDerivAt (fun t : ℝ => z + t • (μ • e)) ((1 : ℝ) • (μ • e)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const (μ • e)).const_add z
  have h1 := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  refine h1.congr_deriv ?_
  rw [one_smul, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, mul_comm]

lemma hasDerivAt_realLine_fderiv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => fderiv ℂ F (z + t • (μ • e)) e) (complexLineSecondDeriv F z e * μ) 0 := by
  have hU : IsOpen {l : ℂ | z + l • e ∈ Ω} := hΩ.preimage (by fun_prop)
  have h0 : (0 : ℂ) ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  have hg : DifferentiableOn ℂ (fun l : ℂ => F (z + l • e)) {l : ℂ | z + l • e ∈ Ω} :=
    hF.comp (by fun_prop) (fun l hl => hl)
  have hg' := hg.deriv hU

  have hder : HasDerivAt (deriv fun l : ℂ => F (z + l • e)) (complexLineSecondDeriv F z e) (((0 : ℝ) : ℂ) * μ) := by
    have h1 := ((hg' 0 h0).differentiableAt (hU.mem_nhds h0)).hasDerivAt
    simpa [complexLineSecondDeriv] using h1
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ) * μ) μ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const μ
  have hcomp := hder.comp (0 : ℝ) hc
  refine hcomp.congr_of_eventuallyEq ?_
  have h0' : ((0 : ℝ) : ℂ) * μ ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0')] with t ht
  show fderiv ℂ F (z + t • (μ • e)) e = deriv (fun l : ℂ => F (z + l • e)) ((t : ℂ) * μ)
  rw [real_smul_smul]
  exact (deriv_slice hΩ hF ht).symm

lemma cauchy_deriv_le {g : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall c R)) (hM : ∀ w ∈ closedBall c R, ‖g w‖ ≤ M) :
    ‖deriv g c‖ ≤ M / R := by
  have hd : DiffContOnCl ℂ g (ball c R) :=
    ⟨hg.mono ball_subset_closedBall, by rw [closure_ball c hR.ne']; exact hg.continuousOn⟩
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd
    (fun w hw => hM w (sphere_subset_closedBall hw))

lemma cauchy_line {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} (he : ‖e‖ = 1) {r M : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ Ω)
    (hM : ∀ w ∈ closedBall z r, ‖F w‖ ≤ M) :
    ‖fderiv ℂ F z e‖ ≤ M / r ∧ ‖complexLineSecondDeriv F z e‖ ≤ 4 * M / r ^ 2 := by
  have hU : IsOpen {l : ℂ | z + l • e ∈ Ω} := hΩ.preimage (by fun_prop)
  have hg : DifferentiableOn ℂ (fun l : ℂ => F (z + l • e)) {l : ℂ | z + l • e ∈ Ω} :=
    hF.comp (by fun_prop) (fun l hl => hl)
  have hball : ∀ l ∈ closedBall (0 : ℂ) r, z + l • e ∈ closedBall z r := by
    intro l hl
    rw [mem_closedBall, dist_eq_norm] at hl ⊢
    simpa [norm_smul, he] using hl
  have hsubU : closedBall (0 : ℂ) r ⊆ {l : ℂ | z + l • e ∈ Ω} := fun l hl => hsub (hball l hl)
  have hM' : ∀ l ∈ closedBall (0 : ℂ) r, ‖F (z + l • e)‖ ≤ M := fun l hl => hM _ (hball l hl)
  have hd0 : deriv (fun l : ℂ => F (z + l • e)) 0 = fderiv ℂ F z e := by
    have h1 := deriv_slice hΩ hF (z := z) (e := e) (l := 0)
      (by simpa using hsub (mem_closedBall_self hr.le))
    simpa using h1
  refine ⟨?_, ?_⟩
  · rw [← hd0]
    exact cauchy_deriv_le hr (hg.mono hsubU) hM'
  · have hr2 : 0 < r / 2 := by positivity

    have hb2 : ∀ w ∈ closedBall (0 : ℂ) (r / 2),
        ‖deriv (fun l : ℂ => F (z + l • e)) w‖ ≤ M / (r / 2) := by
      intro w hw
      have hsub2 : closedBall w (r / 2) ⊆ closedBall (0 : ℂ) r := by
        intro l hl
        rw [mem_closedBall] at hl hw ⊢
        calc dist l 0 ≤ dist l w + dist w 0 := dist_triangle _ _ _
          _ ≤ r / 2 + r / 2 := add_le_add hl hw
          _ = r := by ring
      exact cauchy_deriv_le hr2 ((hg.mono hsubU).mono hsub2) (fun l hl => hM' l (hsub2 hl))
    have hdd := cauchy_deriv_le hr2 ((hg.deriv hU).mono
      (fun l hl => hsubU (closedBall_subset_closedBall (by linarith) hl))) hb2
    show ‖deriv (deriv fun l : ℂ => F (z + l • e)) 0‖ ≤ 4 * M / r ^ 2
    calc ‖deriv (deriv fun l : ℂ => F (z + l • e)) 0‖ ≤ M / (r / 2) / (r / 2) := hdd
      _ = 4 * M / r ^ 2 := by field_simp; ring

lemma measurable_mul_complexLineSecondDeriv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (e : V n) {χ : V n → ℂ} (hχ : Measurable χ)
    (hχΩ : ∀ z, χ z ≠ 0 → z ∈ Ω) : Measurable (fun z => χ z * complexLineSecondDeriv F z e) := by

  have hΦ : Measurable (fun w => fderiv ℂ F w e) := measurable_fderiv_apply_const ℂ F e
  have hu0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_compl_singleton_iff.2 (by positivity)⟩
  refine measurable_of_tendsto_metrizable
    (f := fun (k : ℕ) z => χ z * ((1 / ((k : ℝ) + 1))⁻¹ •
      (fderiv ℂ F (z + (1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)) e - fderiv ℂ F z e)))
    (fun k => ?_) (tendsto_pi_nhds.2 fun z => ?_)
  · refine hχ.mul ?_
    have hm := ((hΦ.comp (measurable_add_const ((1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)))).sub hΦ).const_smul
      ((1 / ((k : ℝ) + 1))⁻¹)
    exact hm
  · by_cases hz : χ z = 0
    · simp only [hz, zero_mul]
      exact tendsto_const_nhds
    · have hd := hasDerivAt_realLine_fderiv hΩ hF (hχΩ z hz) e 1
      have hs := (hd.tendsto_slope_zero.comp hu0).const_mul (χ z)
      simpa using hs

end

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffStatement
section
namespace ReciprocityTheory.L2DbarEstimates.C

open Set
open scoped ContDiff

def HoloSmoothStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω → ContDiffOn ℝ ∞ f Ω

def HoloDerivStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω →
      ∀ v : EuclideanSpace ℂ (Fin n), DifferentiableOn ℂ (fun x => fderiv ℂ f x v) Ω

def HoloContDiffStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω → ContDiffOn ℂ ∞ f Ω

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ident : IdentStatement := by
  intro n Ω F a hΩ hc hF ha h0 x hx
  set L : ℂ → V n := fun t => a + t • (x - a) with hL
  have hLd : Differentiable ℂ L := (differentiable_const a).add (differentiable_id.smul_const (x - a))
  have hLc : Continuous L := hLd.continuous
  set U : Set ℂ := L ⁻¹' Ω with hU
  have hUo : IsOpen U := hΩ.preimage hLc
  have hUconv : Convex ℝ U := by
    intro t1 ht1 t2 ht2 s1 s2 hs1 hs2 hs
    show L (s1 • t1 + s2 • t2) ∈ Ω
    have key : L (s1 • t1 + s2 • t2) = s1 • L t1 + s2 • L t2 := by
      have e : s1 • L t1 + s2 • L t2 = (s1 + s2) • a + (s1 • t1 + s2 • t2) • (x - a) := by
        simp only [hL, smul_add, add_smul, smul_assoc]
        abel
      rw [e, hs, one_smul]
    rw [key]
    exact hc ht1 ht2 hs1 hs2 hs
  have hG : DifferentiableOn ℂ (F ∘ L) U := hF.comp hLd.differentiableOn (fun t ht => ht)
  have hA : AnalyticOnNhd ℂ (F ∘ L) U := hG.analyticOnNhd hUo
  have h0U : (0 : ℂ) ∈ U := by
    show L 0 ∈ Ω
    simpa [hL] using ha
  have h1U : (1 : ℂ) ∈ U := by
    show L 1 ∈ Ω
    simpa [hL] using hx
  have hL0 : L 0 = a := by simp [hL]
  have hev : F ∘ L =ᶠ[𝓝 0] 0 := by
    have ht : Filter.Tendsto L (𝓝 0) (𝓝 a) := by
      rw [← hL0]
      exact hLc.continuousAt.tendsto
    exact ht.eventually h0
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv.isPreconnected h0U hev
  have h1 := hEq h1U
  simpa [hL] using h1

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegGlue
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ae_eq_eqOn {n : ℕ} {Ω : Set (V n)} {U U' : V n → ℂ} (hΩ : IsOpen Ω)
    (hU : ContinuousOn U Ω) (hU' : ContinuousOn U' Ω) (h : U =ᵐ[volume.restrict Ω] U') :
    EqOn U U' Ω := by
  exact Measure.eqOn_open_of_ae_eq h hΩ hU hU'

theorem reg_glue {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ball x r ⊆ Ω ∧
      ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball x r) ∧ u =ᵐ[volume.restrict (ball x r)] U) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ u =ᵐ[volume.restrict Ω] U := by
  classical
  choose! r hr hsub U hU hae using hloc
  have agree : ∀ x ∈ Ω, ∀ y ∈ Ω, EqOn (U x) (U y) (ball x (r x) ∩ ball y (r y)) := by
    intro x hx y hy
    apply ae_eq_eqOn (isOpen_ball.inter isOpen_ball)
    · exact ((hU x hx).mono inter_subset_left).continuousOn
    · exact ((hU y hy).mono inter_subset_right).continuousOn
    · have h1 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U x :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae x hx)
      have h2 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U y :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae y hy)
      exact h1.symm.trans h2
  have loc : ∀ y ∈ Ω, ∀ x ∈ ball y (r y), U x x = U y x := by
    intro y hy x hx
    have hxΩ : x ∈ Ω := hsub y hy hx
    exact agree x hxΩ y hy ⟨mem_ball_self (hr x hxΩ), hx⟩
  refine ⟨fun x => U x x, ?_, ?_⟩
  · intro y hy
    have hnhds : ball y (r y) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hr y hy))
    have hev : (fun x => U x x) =ᶠ[𝓝 y] U y :=
      Filter.eventually_of_mem hnhds (fun x hx => loc y hy x hx)
    exact (((hU y hy).differentiableAt hnhds).congr_of_eventuallyEq hev).differentiableWithinAt
  · obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : Ω => ball (x : V n) (r x)) (fun _ => isOpen_ball)
    have hcov : Ω = ⋃ x ∈ T, ball ((x : Ω) : V n) (r x) := by
      rw [hT]
      ext z
      simp only [mem_iUnion]
      constructor
      · intro hz
        exact ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩
      · rintro ⟨x, hx⟩
        exact hsub x x.2 hx
    rw [hcov, Filter.EventuallyEq, ae_restrict_biUnion_iff _ hTc]
    intro x _
    filter_upwards [hae x x.2, self_mem_ae_restrict (measurableSet_ball (x := (x : V n)) (ε := r x))]
      with z hz hzb
    rw [hz]
    exact (loc x x.2 z hzb).symm

end ReciprocityTheory.L2DbarEstimates.C
end

