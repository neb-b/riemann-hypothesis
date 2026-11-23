module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.AbsZetaPrimeSumErrorLeOfOneLe
section
open Complex

noncomputable section

namespace Formalism.ZF

open ArithmeticFunction in
theorem zetaPrimeSum_nonneg_and_le (y : ℝ) (hy : 1 ≤ y) :
    0 ≤ Formalism.Sz y ∧ Formalism.Sz y ≤ y * y * Real.log y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, 0 ≤ ArithmeticFunction.vonMangoldt n * (y / n - 1) ∧
      ArithmeticFunction.vonMangoldt n * (y / n - 1) ≤ Real.log y * y := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn2).trans (Nat.floor_le hy0)
    have h1 : 0 ≤ y / n - 1 := by
      rw [sub_nonneg, le_div_iff₀ hnpos]
      linarith
    have h2 : y / n - 1 ≤ y := by
      have : y / n ≤ y := div_le_self hy0 hn1'
      linarith
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log y :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hny)
    exact ⟨mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h1, mul_le_mul hΛ h2 h1 hlog⟩
  unfold Formalism.Sz
  refine ⟨Finset.sum_nonneg fun n hn => (hterm n hn).1, ?_⟩
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Real.log y * y := Finset.sum_le_sum fun n hn => (hterm n hn).2
    _ = (⌊y⌋₊ : ℝ) * (Real.log y * y) := by simp
    _ ≤ y * (Real.log y * y) := mul_le_mul_of_nonneg_right (Nat.floor_le hy0) (mul_nonneg hlog hy0)
    _ = y * y * Real.log y := by ring

theorem abs_zetaPrimeSumError_le_of_one_le (y : ℝ) (hy : 1 ≤ y) :
    |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) := by
  obtain ⟨hS0, hS1⟩ := zetaPrimeSum_nonneg_and_le y hy
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hp1 : 0 ≤ y * Real.log y := mul_nonneg hy0 hlog
  have hp2 : 0 ≤ y * (y * Real.log y) := mul_nonneg hy0 hp1
  have hγy : Real.eulerMascheroniConstant * y ≤ y := by nlinarith
  have hγy0 : 0 ≤ Real.eulerMascheroniConstant * y := by nlinarith
  unfold Formalism.Gz
  rw [abs_le]
  constructor <;> nlinarith

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.IntegralEqIntervalIntegralAddCompl
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_sub_le_of_rectangle_identity (Sz R V0 V1 E a b : ℂ) (hS : Sz = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Sz - R‖ ≤ ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h1 : (2 * Real.pi : ℂ) * (Sz - R) = (V0 - 2 * Real.pi * R) + E := by
    rw [hS]; field_simp; ring
  have h2 : I * (V0 - 2 * Real.pi * R) = -(a - b - I * V1) := by linear_combination hrect
  have h3 : ‖V0 - 2 * Real.pi * R‖ = ‖a - b - I * V1‖ := by
    have := congrArg norm h2
    rwa [norm_mul, Complex.norm_I, one_mul, norm_neg] at this
  have h4 : ‖(2 * Real.pi : ℂ) * (Sz - R)‖ = 2 * Real.pi * ‖Sz - R‖ := by
    rw [norm_mul]
    congr 1
    have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [← h4, h1]
  calc ‖V0 - 2 * Real.pi * R + E‖ ≤ ‖V0 - 2 * Real.pi * R‖ + ‖E‖ := norm_add_le _ _
    _ = ‖a - b - I * V1‖ + ‖E‖ := by rw [h3]
    _ ≤ (‖a‖ + ‖b‖ + ‖V1‖) + ‖E‖ := by
        gcongr
        calc ‖a - b - I * V1‖ ≤ ‖a - b‖ + ‖I * V1‖ := norm_sub_le _ _
          _ ≤ ‖a‖ + ‖b‖ + ‖V1‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]; gcongr; exact norm_sub_le _ _
    _ = ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by ring

theorem integral_eq_intervalIntegral_add_compl (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Set.Ioc (-T) T)ᶜ, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hf]

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
section
open Complex Filter Topology Metric

noncomputable section

namespace Formalism.ZF

private theorem hasDerivAt_sub_pow_of_sub_ne_zero (a z : ℂ) (n : ℕ) (h : z - a ≠ 0) :
    HasDerivAt (fun w => (w - a) ^ n) ((z - a) ^ n * ((n : ℂ) / (z - a))) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z :=
    (hasDerivAt_pow n (z - a)).comp z h1
  refine h2.congr_deriv ?_
  rcases n with _ | k
  · simp
  · rw [pow_succ, Nat.add_sub_cancel]
    have hinv : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ h
    linear_combination (-((z - a) ^ k * ((k + 1 : ℕ) : ℂ))) * hinv

private theorem hasDerivAt_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    HasDerivAt (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (z - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) z := by
  classical
  revert hz
  induction Z using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | insert =>
    rename_i a s ha ih
    intro hz
    have hs : ∀ ρ ∈ s, z - ρ ≠ 0 := fun ρ hρ => hz ρ (Finset.mem_insert_of_mem hρ)
    have hza : z - a ≠ 0 := hz a (Finset.mem_insert_self a s)
    have hd := (hasDerivAt_sub_pow_of_sub_ne_zero a z (m a) hza).mul (ih hs)
    beta_reduce at hd
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    refine hd.congr_deriv ?_
    ring

lemma landauLocal_logDeriv_prod (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_apply, (hasDerivAt_prod_sub_pow Z m z hz).deriv]
  have hP : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hz ρ hρ)
  exact (div_eq_iff hP).mpr (mul_comm _ _)

private theorem pow_le_pow_left_of_nonneg_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (le_trans (pow_nonneg ha k) ih)

private theorem norm_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) :
    ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖w - ρ‖ ^ m ρ := by
  simp only [norm_prod, norm_pow]

private theorem div_add_div_sub_eq_div (P S H D : ℂ) (hP : P ≠ 0) (hH : H ≠ 0) :
    (P * S * H + P * D) / (P * H) - S = D / H := by
  rw [sub_eq_iff_eq_add, div_eq_iff (mul_ne_zero hP hH)]
  have hHH : H⁻¹ * H = 1 := inv_mul_cancel₀ hH
  linear_combination (-(P * D)) * hHH

theorem localZeroExpansionOfFactorization : LandauLocalOf := by
  unfold LandauLocalOf LandauLocal
  intro hfac hlog f z₀ r M hr hM hf hf0 hbound
  classical
  have hr3 : 0 < r / 3 := by positivity
  obtain ⟨Z, m, h, hZ, hm, hh, hh0, hfeq⟩ := hfac f z₀ r (r / 3) hr3 (by linarith) hf hf0
  have hZball : ∀ ρ ∈ Z, ‖ρ - z₀‖ ≤ r / 3 := fun ρ hρ => by
    have := ((hZ ρ).1 hρ).1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hZzero : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => ((hZ ρ).1 hρ).2
  have hz₀mem : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hfz₀ := hfeq z₀ hz₀mem
  have hhz₀ : h z₀ ≠ 0 := by
    intro h0; apply hf0; rw [hfz₀, h0, mul_zero]
  have hPz₀le : ‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (norm_nonneg _) _) ?_
    intro ρ hρ
    have h1 : ‖z₀ - ρ‖ ≤ r / 3 := by rw [norm_sub_rev]; exact hZball ρ hρ
    exact pow_le_pow_left_of_nonneg_le (norm_nonneg _) h1 _
  have hPw : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ := by
    intro w hw
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (by linarith) _) ?_
    intro ρ hρ
    have h2 := hZball ρ hρ
    have h3 : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := by
      have := norm_add_le (w - ρ) (ρ - z₀)
      rwa [sub_add_sub_cancel] at this
    have h1 : 2 * r / 3 ≤ ‖w - ρ‖ := by linarith
    exact pow_le_pow_left_of_nonneg_le (by linarith) h1 _
  have key_sphere : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ ≤ M * ‖h z₀‖ := by
    intro w hw
    have hwmem : w ∈ Metric.closedBall z₀ r :=
      Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hw.le)
    have e1 := hbound w hwmem
    rw [hfeq w hwmem, hfz₀, norm_mul, norm_mul] at e1
    have e2 := hPw w hw
    have hq : 0 < (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by positivity
    have e3 : (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) = (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
      rw [mul_div_assoc, mul_pow]
    have e4 : (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
        ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by
      calc (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
          = (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ := by rw [e3]; ring
        _ ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ * ‖h w‖ := mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ M * (‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ * ‖h z₀‖) := e1
        _ ≤ M * ((r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h z₀‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            exact mul_le_mul_of_nonneg_right hPz₀le (norm_nonneg _)
        _ = (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by ring
    exact le_of_mul_le_mul_left e4 hq
  have hdc : DiffContOnCl ℂ h (Metric.ball z₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hr.ne']
    exact hh
  have hmax : ∀ z ∈ Metric.closedBall z₀ r,
      ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    intro z hz
    have hz' : z ∈ closure (Metric.ball z₀ r) := by rwa [closure_ball z₀ hr.ne']
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc ?_ hz'
    intro w hw
    rw [frontier_ball z₀ hr.ne', mem_sphere_iff_norm] at hw
    rw [le_div_iff₀ (by positivity), mul_comm (‖h w‖)]
    exact key_sphere w hw
  have h2N : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have := hmax z₀ hz₀mem
    have hpos : 0 < ‖h z₀‖ := norm_pos_iff.mpr hhz₀
    rw [le_div_iff₀ (by positivity), mul_comm M] at this
    exact le_of_mul_le_mul_left this hpos
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  have h2N1 : (1 : ℝ) ≤ (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    simpa using pow_le_pow_left_of_nonneg_le (a := 1) (b := 2) zero_le_one one_le_two (∑ ρ ∈ Z, m ρ)
  have hhb : ∀ z ∈ Metric.closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := by
    intro z hz
    have hz' : z ∈ Metric.closedBall z₀ r := Metric.closedBall_subset_closedBall (by linarith) hz
    have h1 := hmax z hz'
    have h2 : M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M * ‖h z₀‖ :=
      div_le_self (mul_nonneg (by linarith) (norm_nonneg _)) h2N1
    linarith
  have hlogb := hlog h z₀ (r / 3) M hr3 hM
    (hh.mono (Metric.closedBall_subset_closedBall (by linarith))) hh0 hhb
  refine ⟨Z, m, hZ, hm, hsum, ?_⟩
  intro z hz hfz
  have hzr : z ∈ Metric.ball z₀ r := by
    rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have hnhds : Metric.closedBall z₀ r ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzr) Metric.ball_subset_closedBall
  have hev : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w :=
    Filter.mem_of_superset hnhds (fun w hw => hfeq w hw)
  have hfeqz := hfeq z (Metric.ball_subset_closedBall hzr)
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, zero_mul]
  have hhz : h z ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, mul_zero]
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := by
    intro ρ hρ h0; apply hfz; rw [sub_eq_zero.mp h0]; exact hZzero ρ hρ
  have hPd := hasDerivAt_prod_sub_pow Z m z hzρ
  have hhd : HasDerivAt h (deriv h z) z := (hh.differentiableAt hnhds).hasDerivAt
  have hd := (hPd.mul hhd).congr_of_eventuallyEq hev
  have hsplit : deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) = deriv h z / h z := by
    rw [hd.deriv, hfeqz]
    exact div_add_div_sub_eq_div _ _ _ _ hPz hhz
  rw [hsplit]
  have hz6 : z ∈ Metric.closedBall z₀ (r / 3 / 2) := by
    rw [Metric.mem_closedBall] at hz ⊢; linarith
  calc ‖deriv h z / h z‖ ≤ 24 * Real.log M / (r / 3) := hlogb z hz6
    _ = 72 * Real.log M / r := by rw [div_div_eq_mul_div]; ring

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LaurentAtOne
section
open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

def laHfun (y : ℝ) (s : ℂ) : ℂ :=
  (1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s)) * ((y : ℂ) ^ s / s)

def laU : Set ℂ := {s | riemannZeta₁ s ≠ 0} ∩ {s | s ≠ 0}

theorem laU_open : IsOpen laU :=
  (isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const).inter isOpen_ne

theorem one_mem_laU : (1 : ℂ) ∈ laU := by simp [laU]

theorem laH_diffOn (y : ℝ) (hy : 0 < y) : DifferentiableOn ℂ (laHfun y) laU := by
  intro s hs
  have hZ : riemannZeta₁ s ≠ 0 := hs.1
  have h0 : s ≠ 0 := hs.2
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  apply DifferentiableAt.differentiableWithinAt
  have hd : DifferentiableAt ℂ (deriv riemannZeta₁) s := differentiable_riemannZeta₁.deriv s
  have hz : DifferentiableAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁ s
  have hc : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hy0)
  exact ((differentiableAt_const _).sub ((differentiableAt_id.sub_const 1).mul
    (hd.div hz hZ))).mul (hc.div differentiableAt_id h0)

theorem laH_one (y : ℝ) : laHfun y 1 = y := by simp [laHfun]

theorem laH_deriv_one (y : ℝ) (hy : 0 < y) :
    deriv (laHfun y) 1 = (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hB : DifferentiableAt ℂ (fun s => deriv riemannZeta₁ s / riemannZeta₁ s) 1 :=
    (differentiable_riemannZeta₁.deriv 1).div (differentiable_riemannZeta₁ 1) (by simp)
  have hk := (((hasDerivAt_id' (1 : ℂ)).sub_const 1).mul hB.hasDerivAt).const_sub 1
  have hc : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (1 : ℂ) * Complex.log y) 1 := by
    simpa using (hasStrictDerivAt_const_cpow (x := (y : ℂ)) (y := 1) (Or.inl hy0)).hasDerivAt
  have hg := hc.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have hh := hk.mul hg
  have hh' : HasDerivAt (laHfun y) _ 1 := hh
  rw [hh'.deriv]
  rw [← Complex.ofReal_log hy.le]
  simp
  ring

theorem laurentExpansionAtOne : LaurentAtOne := by
  intro y hy
  set h := laHfun y with hdef
  have hn : laU ∈ 𝓝 (1 : ℂ) := laU_open.mem_nhds one_mem_laU
  refine ⟨dslope (dslope h 1) 1, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (dslope (dslope h 1) 1) laU :=
      (differentiableOn_dslope hn).2 ((differentiableOn_dslope hn).2 (laH_diffOn y hy))
    exact h1.differentiableAt hn
  · have hU : ∀ᶠ w in 𝓝[≠] (1 : ℂ), w ∈ laU := nhdsWithin_le_nhds hn
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add, hU, self_mem_nhdsWithin]
      with w hw hwU hw1
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
    have hw0 : w ≠ 0 := hwU.2
    have e1 := sub_smul_dslope h 1 w
    have e2 := sub_smul_dslope (dslope h 1) 1 w
    rw [dslope_same] at e2
    simp only [smul_eq_mul] at e1 e2
    rw [hdef, laH_deriv_one y hy] at e2
    rw [hdef, laH_one y] at e1
    have hhw : laHfun y w =
        (1 - (w - 1) * (deriv riemannZeta₁ w / riemannZeta₁ w)) * ((y : ℂ) ^ w / w) := rfl
    unfold Fy
    rw [hw]
    rw [hdef] at *
    generalize deriv riemannZeta₁ w / riemannZeta₁ w = B at hhw ⊢
    generalize (y : ℂ) ^ w = P at hhw ⊢
    generalize dslope (dslope (laHfun y) 1) 1 w = q at e2 ⊢
    generalize dslope (laHfun y) 1 w = D at e1 e2
    generalize laHfun y w = H at e1 hhw
    have key : (1 - (w - 1) * B) * (P / w) =
        y + (w - 1) * (((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)
          + (w - 1) * q) := by
      rw [← hhw]; linear_combination -e1 - (w - 1) * e2
    have lhs : -(-(w - 1)⁻¹ + B) * P / (w * (w - 1)) =
        (1 - (w - 1) * B) * (P / w) / (w - 1) ^ 2 := by
      field_simp
      ring
    rw [lhs, key]
    field_simp
    ring

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
section
open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zflb_exists_log {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  obtain ⟨g, hg₀, hg⟩ := ((hf.deriv isOpen_ball).div hf hne).isExactOn_ball.with_val_at z₀ 0
  refine ⟨g, hg₀, hg, ?_⟩
  have hd : DifferentiableOn ℂ g (ball z₀ R) :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hf hd.cexp isOpen_ball isPreconnected_ball
    (fun _ _ => Complex.exp_ne_zero _) hne).mp fun z hz => by
      simp [logDeriv_apply, (hg z hz).cexp.deriv]
  intro z hz
  have hcenter := hc (mem_ball_self (pos_of_mem_ball hz))
  have hfc : f z₀ = c := by simpa [hg₀] using hcenter
  simpa [hfc] using hc hz

theorem logDerivBoundOnBall : LogDerivBound := by
  intro f z₀ R M hR hM hf hne hbd z hz
  have hR0 : R ≠ 0 := hR.ne'
  have hfb : DifferentiableOn ℂ f (ball z₀ R) := hf.mono ball_subset_closedBall
  have hneb : ∀ w ∈ ball z₀ R, f w ≠ 0 := fun w hw => hne w (ball_subset_closedBall hw)
  obtain ⟨g, hg0, hgd, hgf⟩ := zflb_exists_log hfb hneb
  have hf0 : 0 < ‖f z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hR.le))
  have hre : ∀ w ∈ ball z₀ R, (g w).re ≤ Real.log M := by
    intro w hw
    have h1 := hbd w (ball_subset_closedBall hw)
    rw [hgf w hw, norm_mul, Complex.norm_exp] at h1
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le zero_lt_one hM)).2
      ((mul_le_mul_iff_right₀ hf0).mp (by simpa only [mul_comm M] using h1))
  have hzb : dist z z₀ ≤ R / 2 := hz
  have hshift : ∀ v ∈ ball (0 : ℂ) R, z₀ + v ∈ ball z₀ R := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.1 hv
  have hmain : ∀ A : ℝ, Real.log M < A → ‖deriv f z / f z‖ ≤ 24 * A / R := by
    intro A hA
    have hA0 : 0 < A := lt_of_le_of_lt (Real.log_nonneg hM) hA
    have hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 R) := by
      intro v hv
      exact ((hgd _ (hshift v hv)).differentiableAt.comp v
        (differentiableAt_id.const_add z₀)).differentiableWithinAt
    have hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 R) {w | w.re ≤ A} := by
      intro v hv
      exact le_trans (hre _ (hshift v hv)) hA.le
    have hbc : ∀ w ∈ closedBall z₀ (3 * R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      obtain ⟨u, rfl⟩ : ∃ u, w = z₀ + u := ⟨w - z₀, by ring⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hw
      have huR : u ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        linarith
      have hB : ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) :=
        Complex.borelCaratheodory_zero hA0 hhd hhm hR huR (by simpa using hg0)
      have hpos : 0 < R - ‖u‖ := by linarith
      calc ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) := hB
        _ ≤ 6 * A := by
          rw [div_le_iff₀ hpos]
          nlinarith [norm_nonneg u]
    have hR4 : 0 < R / 4 := by linarith
    have hsub : closedBall z (R / 4) ⊆ ball z₀ R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < R := by linarith
    have hdiff : DiffContOnCl ℂ g (ball z (R / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hR4.ne']
      intro w hw
      exact (hgd w (hsub hw)).differentiableAt.differentiableWithinAt
    have hC : ∀ w ∈ sphere z (R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      apply hbc
      rw [mem_sphere] at hw
      rw [mem_closedBall]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 3 * R / 4 := by linarith
    have hzb' : z ∈ ball z₀ R := hsub (mem_closedBall_self hR4.le)
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hdiff hC
    rw [(hgd z hzb').deriv] at hder
    calc ‖deriv f z / f z‖ ≤ 6 * A / (R / 4) := hder
      _ = 24 * A / R := by
        field_simp
        all_goals ring
  apply le_of_forall_pos_le_add
  intro ε hε
  have hεR : 0 < ε * R / 24 := by positivity
  have h := hmain (Real.log M + ε * R / 24) (by linarith)
  calc ‖deriv f z / f z‖ ≤ 24 * (Real.log M + ε * R / 24) / R := h
    _ = 24 * Real.log M / R + ε := by
      field_simp

end Formalism.ZF
end
end

