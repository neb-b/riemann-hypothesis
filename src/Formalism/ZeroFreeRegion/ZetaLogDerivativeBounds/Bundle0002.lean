module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormIntegralComplLe
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_integral_compl_le (f : ℝ → ℂ) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T)
    (hf : ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ B / t ^ 2) :
    ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ 2 * Real.pi * B / T := by
  have hSm : MeasurableSet ((Set.Ioc (-T) T)ᶜ) := measurableSet_Ioc.compl
  have hg_int : Integrable (fun t : ℝ => 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_div hT.ne').const_mul _
  have hbound : ∀ t ∈ (Set.Ioc (-T) T)ᶜ, ‖f t‖ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
    intro t ht
    have hTt : T ≤ |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have ht2 : T ^ 2 ≤ t ^ 2 := by
      have := pow_le_pow_left₀ hT.le hTt 2
      rwa [sq_abs] at this
    have htpos : 0 < t ^ 2 := lt_of_lt_of_le (by positivity) ht2
    calc ‖f t‖ ≤ B / t ^ 2 := hf t hTt
      _ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
        rw [show 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * B / (T ^ 2 + t ^ 2) by
          field_simp]
        rw [div_le_div_iff₀ htpos (by positivity)]
        nlinarith
  have h1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    norm_integral_le_of_norm_le hg_int.integrableOn (ae_restrict_of_forall_mem hSm hbound)
  have h2 : ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ ≤
      ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    setIntegral_le_integral hg_int (Filter.Eventually.of_forall (fun t => by positivity))
  have h3 : ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * Real.pi * B / T := by
    rw [integral_const_mul]
    have e := MeasureTheory.Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) T
    rw [e, integral_univ_inv_one_add_sq, abs_of_pos hT]
    field_simp
    ring
  linarith

theorem pow_three_mul_exp_le (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-(c * s / 4)) ≤ 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by
  have hs0 : 0 ≤ c * s / 8 := by positivity
  have hA : 0 < Real.exp (-(c / 8) * s) := Real.exp_pos _
  have hEA : Real.exp (c * s / 8) * Real.exp (-(c / 8) * s) = 1 := by
    rw [← Real.exp_add, show c * s / 8 + -(c / 8) * s = 0 by ring, Real.exp_zero]
  have hsq : Real.exp (-(c * s / 4)) = Real.exp (-(c / 8) * s) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfact : (c * s / 8) ^ 3 ≤ 6 * Real.exp (c * s / 8) := by
    have h := Real.pow_div_factorial_le_exp (c * s / 8) hs0 3
    norm_num [Nat.factorial] at h
    linarith
  have hkey : (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_right hfact hA.le]
  have hs3 : s ^ 3 = (8 / c) ^ 3 * (c * s / 8) ^ 3 := by
    field_simp
  rw [hsq, hs3]
  have hk : 0 < (8 / c) ^ 3 := by positivity
  calc (8 / c) ^ 3 * (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ^ 2
      = (8 / c) ^ 3 * ((c * s / 8) ^ 3 * Real.exp (-(c / 8) * s)) * Real.exp (-(c / 8) * s) := by ring
    _ ≤ (8 / c) ^ 3 * 6 * Real.exp (-(c / 8) * s) := by gcongr
    _ = 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by ring

theorem log_exp_add_two_bounds (c s : ℝ) (hc : 0 < c) (hs : 8 / c ≤ s) :
    1 ≤ Real.exp (c * s / 4) ∧ 1 ≤ Real.log (Real.exp (c * s / 4) + 2) ∧
      Real.log (Real.exp (c * s / 4) + 2) ≤ c * s / 2 := by
  have hcs : 8 ≤ c * s := by
    rw [div_le_iff₀ hc] at hs
    linarith
  have hE1 : 1 ≤ Real.exp (c * s / 4) := Real.one_le_exp (by linarith)
  have hE2 : Real.exp 2 ≤ Real.exp (c * s / 4) := Real.exp_le_exp.mpr (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨hE1, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · rw [Real.log_le_iff_le_exp (by positivity)]
    have e : Real.exp (c * s / 2) = Real.exp (c * s / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    nlinarith

theorem exp_mul_rpow_le (y c L s : ℝ) (hy : 0 < y) (hℓ : Real.log y = s ^ 2) (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) (hL : 0 < L) (hLs : L ≤ c * s / 2) (hs : 0 < s) :
    Real.exp (c * s / 4) * y ^ (1 - c / L) ≤ y * Real.exp (-(c * s / 4)) := by
  have hy' : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy]
  rw [Real.rpow_def_of_pos hy, hℓ]
  conv_rhs => rw [hy']
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have key : c * s / 2 ≤ s ^ 2 * (c / L) := by
    rw [show s ^ 2 * (c / L) = (c * s ^ 2) / L by ring, le_div_iff₀ hL]
    have hcs : 0 < c * s := mul_pos hc hs
    have hL4 : L ≤ s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hL4 hcs.le]
  nlinarith [key]

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormLogDerivLeLamF
section
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

def lamF (σ : ℝ) : ℝ := ∑' n, ‖term ↗Λ (σ : ℂ) n‖

lemma norm_logDeriv_le_lamF {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ lamF s.re := by
  have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsum : Summable fun n => ‖term ↗Λ s n‖ := summable_norm_iff.2 (LSeriesSummable_vonMangoldt hs)
  have heq : (fun n => ‖term ↗Λ s n‖) = fun n => ‖term ↗Λ ((s.re : ℝ) : ℂ) n‖ := by
    funext n
    rw [norm_term_eq, norm_term_eq]
    simp
  calc ‖deriv riemannZeta s / riemannZeta s‖ = ‖L ↗Λ s‖ := by rw [hL, neg_div, norm_neg]
    _ ≤ ∑' n, ‖term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ = lamF s.re := by rw [heq]; rfl

lemma term_vonMangoldt_real (σ : ℝ) (n : ℕ) :
    term ↗Λ (σ : ℂ) n = ((‖term ↗Λ (σ : ℂ) n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h : term ↗Λ (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast]
    rw [h, Complex.norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]

lemma lamF_eq_norm {σ : ℝ} (hσ : 1 < σ) : lamF σ = ‖L ↗Λ (σ : ℂ)‖ := by
  have h : L ↗Λ (σ : ℂ) = ((lamF σ : ℝ) : ℂ) := by
    rw [LSeries, lamF, Complex.ofReal_tsum]
    exact tsum_congr fun n => term_vonMangoldt_real σ n
  rw [h, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ lamF σ from tsum_nonneg fun n => norm_nonneg _)]

lemma lamF_anti {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : lamF τ ≤ lamF σ := by
  have hs : ∀ x : ℝ, 1 < x → Summable fun n => ‖term ↗Λ (x : ℂ) n‖ := fun x hx =>
    summable_norm_iff.2 (LSeriesSummable_vonMangoldt (by simpa using hx))
  unfold lamF
  refine Summable.tsum_le_tsum (fun n => ?_) (hs τ (by linarith)) (hs σ hσ)
  rw [norm_term_eq, norm_term_eq]
  split_ifs with hn
  · rfl
  · simp only [ofReal_re]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 h)

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectShiftOf
section
open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

lemma rso_zeta_ne_near_one : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 1 → riemannZeta w ≠ 0 := by
  have h := riemannZeta_residue_one.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with w hw hw1 hz
  exact hw hw1 (by rw [hz, mul_zero])

lemma rso_deriv_zeta_diff : DifferentiableOn ℂ (deriv riemannZeta) {w : ℂ | w ≠ 1} := by
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
    fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact hd.deriv isOpen_ne

lemma rso_Fy_diff (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) : DifferentiableAt ℂ (Fy y) w := by
  have hd1 : DifferentiableAt ℂ (deriv riemannZeta) w :=
    rso_deriv_zeta_diff.differentiableAt (isOpen_ne.mem_nhds h1)
  have hd2 : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta h1
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd3 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) w :=
    (differentiableAt_id).const_cpow (Or.inl hy0)
  have hden : w * (w - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  unfold Fy
  exact (((hd1.div hd2 hz).neg).mul hd3).div (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hden

theorem rectangleShiftOfResidue : RectShiftOf := by
  intro hRDP hLA y hy σ₁ σ₀ T h1 h2 h3 hT hz
  obtain ⟨A, hA1, hAev⟩ := hLA y hy
  set a : ℂ := (y : ℂ) with ha
  set b : ℂ := (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y with hb
  let H : ℂ → ℂ := fun w => Fy y w - a / (w - 1) ^ 2 - b / (w - 1)
  let G : ℂ → ℂ := fun w => if w = 1 then A 1 else H w
  have hH : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ H z := by
    intro z hz0 hz1 hzz
    have hzm : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    exact ((rso_Fy_diff y hy hz0 hz1 hzz).sub
      ((differentiableAt_const a).div ((differentiableAt_id.sub_const 1).pow 2) (pow_ne_zero 2 hzm))).sub
      ((differentiableAt_const b).div (differentiableAt_id.sub_const 1) hzm)
  have hG : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ G z := by
    intro z hz0 hz1 hzz
    refine (hH z hz0 hz1 hzz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
    simp [G, hw]
  have hev := hAev
  rw [eventually_nhdsWithin_iff] at hev
  have hG1 : DifferentiableAt ℂ G 1 := by
    refine hA1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with w hw
    by_cases hw1 : w = 1
    · subst hw1; simp [G]
    · have hw' := hw hw1
      simp only [G, H, if_neg hw1]
      rw [hw']
      ring
  set U : Set ℂ := {w | ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z} with hU
  have hUo : IsOpen U := isOpen_setOf_eventually_nhds
  have hUd : DifferentiableOn ℂ G U := fun w hw => (hw.self_of_nhds).differentiableWithinAt
  have h01 : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0 := eventually_ne_nhds one_ne_zero
  have hsub : (Set.uIcc σ₁ σ₀ ×ℂ Set.uIcc (-T) T) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hr1; simp at hr1; linarith
    by_cases hw1 : w = 1
    · subst hw1
      show ∀ᶠ z in 𝓝 (1 : ℂ), DifferentiableAt ℂ G z
      filter_upwards [rso_zeta_ne_near_one, h01] with z hz1 hz0
      by_cases hz1' : z = 1
      · subst hz1'; exact hG1
      · exact hG z hz0 hz1' (hz1 hz1')
    · have hzw : riemannZeta w ≠ 0 := hz w hr1 hr2 (abs_le.2 ⟨hi1, hi2⟩) hw1
      have hc : ContinuousAt riemannZeta w := (differentiableAt_riemannZeta hw1).continuousAt
      show ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z
      filter_upwards [hc.eventually_ne hzw, isOpen_ne.mem_nhds hw1, isOpen_ne.mem_nhds hw0]
        with z hzz hz1 hz0
      exact hG z hz0 hz1 hzz
  refine hRDP (Fy y) G a b 1 σ₁ σ₀ (-T) T (by simpa using h2) (by simpa using h3)
    (by simp; linarith) (by simpa using hT) ⟨U, hUo, hsub, hUd⟩ ?_
  intro w hw
  simp only [G, H, if_neg hw]
  ring

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaNeZeroOfMemRectangle
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_perronIntegrand (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fy y w‖ = ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  simp only [Fy, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy]

theorem one_sub_div_log_le (c c' T v : ℝ) (hc : 0 < c) (hcc : c ≤ c') (hT : 0 ≤ T) (hv : |v| ≤ T) :
    1 - c' / Real.log (|v| + 2) ≤ 1 - c / Real.log (T + 2) := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hv0 : Real.log 2 ≤ Real.log (|v| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg v])
  have hvT : Real.log (|v| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by linarith [abs_nonneg v]) (by linarith)
  have hpos : 0 < Real.log (|v| + 2) := lt_of_lt_of_le h2 hv0
  have e1 : c / Real.log (T + 2) ≤ c / Real.log (|v| + 2) :=
    div_le_div_of_nonneg_left hc.le hpos hvT
  have e2 : c / Real.log (|v| + 2) ≤ c' / Real.log (|v| + 2) :=
    div_le_div_of_nonneg_right hcc hpos.le
  linarith

theorem riemannZeta_ne_zero_of_mem_rectangle (c₀ : ℝ)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (c T σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₀) (hT : 0 ≤ T) :
    ∀ w : ℂ, 1 - c / Real.log (T + 2) ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → w ≠ 1 →
      riemannZeta w ≠ 0 := by
  intro w h1 _ h3 h4
  exact hZ w h4 ((one_sub_div_log_le c c₀ T w.im hc hcc hT h3).trans h1)

theorem norm_perronIntegrand_le_right (C₂ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fy y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
  set w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I with hw
  have hl : 0 < Real.log y := Real.log_pos hy
  have hre : w.re = 1 + 1 / Real.log y := by simp [hw]
  have him : w.im = t := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ Real.log y + C₂ := by
    have := hR w (by rw [hre]; have := one_div_pos.mpr hl; linarith)
    rw [hre] at this
    simpa using this
  have hpow : y ^ w.re = Real.exp 1 * y := by
    rw [hre, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hl.ne']
    ring
  have ht0 : 0 < |t| := lt_of_lt_of_le hT ht
  have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by
    have : (w - 1).im = t := by simp [him]
    rw [← this]; exact Complex.abs_im_le_norm _
  have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hnum : 0 ≤ Real.log y + C₂ := le_trans (norm_nonneg _) hζ
  rw [hpow]
  have htp : 0 < t ^ 2 := by rw [← sq_abs]; exact pow_pos ht0 2
  calc ‖deriv riemannZeta w / riemannZeta w‖ * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖)
      ≤ (Real.log y + C₂) * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
        apply div_le_div_of_nonneg_left (mul_nonneg hnum (by positivity)) htp hden

theorem norm_perronIntegrand_le_horizontal (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T x v σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hx1 : 1 - c / Real.log (T + 2) ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fy y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
  have hre : w.re = x := by simp [hw]
  have him : w.im = v := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hw1 : T ≤ ‖w‖ := by rw [← hv, ← him]; exact Complex.abs_im_le_norm w
  have hw2 : T ≤ ‖w - 1‖ := by
    have : (w - 1).im = v := by simp [him]
    rw [← hv, ← this]; exact Complex.abs_im_le_norm _
  have hne : w ≠ 1 := by
    intro h
    have : (w - 1) = 0 := by rw [h]; ring
    rw [this, norm_zero] at hw2; linarith
  have hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
    rw [hre]
    exact (one_sub_div_log_le c c₁ T w.im hc hcc (by linarith) (by rw [him, hv])).trans hx1
  have hD' := hD w hne hreg
  rw [him, hv] at hD'
  have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := by
    calc ‖deriv riemannZeta w / riemannZeta w‖
        = ‖(deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) - 1 / (w - 1)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := add_le_add hD' hinv
  have hpow : y ^ w.re ≤ y ^ σ₀ := by
    rw [hre]; exact Real.rpow_le_rpow_of_exponent_le hy hx2
  have hden : T ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by nlinarith
  have htp : 0 < T ^ 2 := by positivity
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) htp hden

theorem norm_perronIntegrand_le_left (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T u : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 0 < y) (hT : 0 ≤ T) (hu : |u| ≤ T)
    (hhalf : 1 / 2 ≤ 1 - c / Real.log (T + 2)) :
    ‖Fy y (((1 - c / Real.log (T + 2) : ℝ) : ℂ) + u * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + Real.log (T + 2) / c) * y ^ (1 - c / Real.log (T + 2)) *
        (2 * Real.log (T + 2) / c) := by
  set L := Real.log (T + 2) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  set w : ℂ := (((1 - c / L : ℝ)) : ℂ) + u * I with hw
  have hre : w.re = 1 - c / L := by simp [hw]
  have him : w.im = u := by simp [hw]
  rw [norm_perronIntegrand y hy w]
  have hcL : 0 < c / L := div_pos hc hL
  have hw1 : 1 / 2 ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hre, abs_of_pos (by linarith)] at this; linarith
  have hw2 : c / L ≤ ‖w - 1‖ := by
    have h := Complex.abs_re_le_norm (w - 1)
    have : (w - 1).re = -(c / L) := by simp [hre]
    rw [this, abs_neg, abs_of_pos hcL] at h; exact h
  have hne : w ≠ 1 := by
    intro h
    have : (w - 1) = 0 := by rw [h]; ring
    rw [this, norm_zero] at hw2; linarith
  have hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
    rw [hre, him]
    exact one_sub_div_log_le c c₁ T u hc hcc hT hu
  have hD' := hD w hne hreg
  rw [him] at hD'
  have hlogu : Real.log (|u| + 2) ^ 2 ≤ L ^ 2 := by
    have h0 : 0 ≤ Real.log (|u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
    have h1 : Real.log (|u| + 2) ≤ L := Real.log_le_log (by linarith [abs_nonneg u]) (by linarith)
    exact pow_le_pow_left₀ h0 h1 2
  have hinv : ‖1 / (w - 1)‖ ≤ L / c := by
    rw [norm_div, norm_one]
    have : 0 < ‖w - 1‖ := lt_of_lt_of_le hcL hw2
    rw [div_le_div_iff₀ this hc]
    have := mul_le_mul_of_nonneg_left hw2 hL.le
    rw [mul_div_cancel₀ _ hL.ne'] at this
    linarith
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * L ^ 2 + L / c := by
    calc ‖deriv riemannZeta w / riemannZeta w‖
        = ‖(deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) - 1 / (w - 1)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ ≤ C₁ * L ^ 2 + L / c := add_le_add (hD'.trans (mul_le_mul_of_nonneg_left hlogu hC₁)) hinv
  have hden : c / (2 * L) ≤ ‖w‖ * ‖w - 1‖ := by
    have : c / (2 * L) = (1 / 2) * (c / L) := by field_simp
    rw [this]
    exact mul_le_mul hw1 hw2 hcL.le (by linarith)
  have hden0 : 0 < c / (2 * L) := by positivity
  rw [hre]
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (c / (2 * L)) := by
        apply div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ = (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) * (2 * L / c) := by
        field_simp

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeight
section
open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

theorem zeroFreeBoundedHeight : SmallHeight := by
  unfold SmallHeight
  intro T
  have hopen : IsOpen {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    by_cases hz1 : z = 1
    · subst hz1
      have h := riemannZeta_residue_one.eventually_ne one_ne_zero
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with x hx hx1
      exact right_ne_zero_of_mul (hx hx1)
    · have hc : ContinuousAt riemannZeta z := (differentiableAt_riemannZeta hz1).continuousAt
      filter_upwards [hc.eventually_ne (hz hz1)] with x hx _
      exact hx
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) '' Icc (-T) T
  have hKc : IsCompact K :=
    isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hKsub : K ⊆ {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩ _
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hopen hKsub
  refine ⟨δ, hδ, fun s hs hre hs1 => ?_⟩
  by_cases hle : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hle
  · push_neg at hle
    have hp : (1 : ℂ) + (s.im : ℂ) * I ∈ K := ⟨s.im, abs_le.mp hs, rfl⟩
    have hre1 : ((1 : ℂ) + (s.im : ℂ) * I).re = 1 := by simp
    have him1 : s.im = ((1 : ℂ) + (s.im : ℂ) * I).im := by simp
    have hd : dist s ((1 : ℂ) + (s.im : ℂ) * I) ≤ δ := by
      rw [Complex.dist_of_im_eq him1, Real.dist_eq, hre1, abs_le]
      constructor <;> linarith
    exact hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hp hd) hs1

end Formalism.ZF
end
end

