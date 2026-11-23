module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
section
open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma three_le_modulus_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 3 ≤ q := by
  by_contra h
  push_neg at h
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  interval_cases q
  all_goals
    apply hχ
    ext a
    have ha : a = 1 := by revert a; decide
    rw [ha]
    simp

lemma two_le_log_three_mul (q : ℕ) (hq : 3 ≤ q) : 2 ≤ Real.log (3 * q) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; try norm_num
  rw [Real.le_log_iff_exp_le (by positivity), e2]
  nlinarith

private lemma rpow_le_exp_three_halves_of_le_log (q : ℕ) (hq : 3 ≤ q) (x t : ℝ) (hx : 1 ≤ x) (hxq : x ≤ 3 * q)
    (ht : t ≤ 3 / (2 * Real.log (3 * q))) : x ^ t ≤ Real.exp (3 / 2) := by
  have hL : 2 ≤ Real.log (3 * q) := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlxL : Real.log x ≤ Real.log (3 * q) := Real.log_le_log hx0 hxq
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.2
  have h1 : Real.log x * t ≤ Real.log x * (3 / (2 * Real.log (3 * q))) := mul_le_mul_of_nonneg_left ht hlx
  have h2 : Real.log x * (3 / (2 * Real.log (3 * q))) ≤ Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) :=
    mul_le_mul_of_nonneg_right hlxL (by positivity)
  have h3 : Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) = 3 / 2 := by field_simp; try ring
  linarith

lemma rpow_neg_le_exp_inv_near_one (q : ℕ) (hq : 3 ≤ q) (x : ℝ) (hx : 1 ≤ x) (hxq : x ≤ q) (r : ℝ)
    (hr : 1 - 3 / (2 * Real.log (3 * q)) ≤ r) :
    x ^ (-r) ≤ Real.exp (3 / 2) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hqR : (0 : ℝ) ≤ q := by positivity
  have e : x ^ (-r) = x ^ (1 - r) * x⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (rpow_le_exp_three_halves_of_le_log q hq x (1 - r) hx (by linarith) (by linarith))
    (inv_nonneg.2 hx0.le)

lemma partial_sum_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) :
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (1 + Real.log (3 * q)) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (n : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    have hχn : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hr := rpow_neg_le_exp_inv_near_one q hq n (by exact_mod_cast h1) (by exact_mod_cast h2) w.re hw
    calc ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-w.re) ≤ 1 * (Real.exp (3 / 2) * (n : ℝ)⁻¹) :=
          mul_le_mul hχn hr (by positivity) zero_le_one
      _ = _ := one_mul _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hH : ∑ n ∈ Icc 1 q, ((n : ℝ))⁻¹ = (harmonic q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [hH]
  refine (harmonic_le_one_add_log q).trans ?_
  have : Real.log q ≤ Real.log (3 * q) := Real.log_le_log (by positivity) (by linarith)
  linarith

lemma lfunction_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) (hw4 : 1 / 4 ≤ w.re) (hw2 : ‖w‖ ≤ 2) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hre0 : 0 < w.re := by linarith
  have hB : ∀ M, ‖Formalism.FX.LFunctionPartialSum.Ap χ M‖ ≤ (q : ℝ) + 1 := fun M => norm_character_sum_Icc_le χ hχ M
  have hpos : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have hx1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith
  have hx3 : (q : ℝ) + 1 ≤ 3 * q := by linarith
  have hpow : ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) ≤ Real.exp (3 / 2) := by
    have := rpow_le_exp_three_halves_of_le_log q hq ((q : ℝ) + 1) (1 - w.re) hx1 hx3 (by linarith)
    rwa [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one] at this
  rw [Formalism.FX.LFunctionPartialSum.LFunction_eq_G (χ := χ) hχ hB hre0]
  unfold Formalism.FX.LFunctionPartialSum.G
  rw [← Summable.sum_add_tsum_nat_add (q + 1) (Formalism.FX.LFunctionPartialSum.summable_dterm (χ := χ) hB hre0),
    eq_sub_of_add_eq (Formalism.FX.LFunctionPartialSum.partial_identity (χ := χ) w q)]
  have h1 := partial_sum_norm_le_near_one χ hq w hw
  have h2 : ‖Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w)‖ ≤ Real.exp (3 / 2) := by
    rw [norm_mul]
    have e : ((q : ℂ) + 1) = ((q + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    push_cast
    calc ‖Formalism.FX.LFunctionPartialSum.Ap χ q‖ * ((q : ℝ) + 1) ^ (-w.re) ≤ ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) :=
          mul_le_mul_of_nonneg_right (hB q) (by positivity)
      _ ≤ _ := hpow
  have h3 : ‖∑' i, Formalism.FX.LFunctionPartialSum.dterm χ w (i + (q + 1))‖ ≤ 8 * Real.exp (3 / 2) := by
    refine (Formalism.FX.LFunctionPartialSum.norm_tail_le χ hB hre0 q).trans ?_
    have hw' : ‖w‖ / w.re ≤ 8 := by rw [div_le_iff₀ hre0]; linarith
    calc ((q : ℝ) + 1) * (‖w‖ / w.re) * ((q : ℝ) + 1) ^ (-w.re)
        = (‖w‖ / w.re) * (((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re)) := by ring
      _ ≤ 8 * Real.exp (3 / 2) := mul_le_mul hw' hpow (by positivity) (by norm_num)
  have hsub := norm_sub_le (∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)) (Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w))
  refine (norm_add_le _ _).trans ?_
  have he := Real.exp_pos (3 / 2)
  have hk := mul_le_mul_of_nonneg_left (show 10 + Real.log (3 * q) ≤ 38 * Real.log (3 * q) by linarith) he.le
  nlinarith

theorem lfunction_deriv_near_one : LDerivNearOne := by
  refine ⟨76 * Real.exp (3 / 2), fun q _ χ hχ σ hσ1 hσ2 => ?_⟩
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hρ : 0 < 1 / (2 * Real.log (3 * q)) := by positivity
  have hd : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (Metric.ball (σ : ℂ) (1 / (2 * Real.log (3 * q)))) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hC : ∀ z ∈ Metric.sphere (σ : ℂ) (1 / (2 * Real.log (3 * q))),
      ‖DirichletCharacter.LFunction χ z‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre : |(z - σ).re| ≤ 1 / (2 * Real.log (3 * q)) := by rw [← hz]; exact Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have h1 : 1 / Real.log (3 * q) ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    have h2 : 1 / (2 * Real.log (3 * q)) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    have e3 : 3 / (2 * Real.log (3 * q)) = 1 / Real.log (3 * q) + 1 / (2 * Real.log (3 * q)) := by
      field_simp
      try ring
    have hab := abs_le.1 hre
    apply lfunction_norm_le_near_one χ hχ z
    · rw [e3]; linarith
    · linarith
    · calc ‖z‖ = ‖(z - σ) + σ‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - σ‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 := by
          rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        _ ≤ 2 := by norm_num
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd hC
  calc _ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) / (1 / (2 * Real.log (3 * q))) := this
    _ = 76 * Real.exp (3 / 2) * Real.log (3 * q) ^ 2 := by field_simp; try ring

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLemmaLfunctionZeros
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma landau_lemma_lfunction_zeros (hLL : LandauLocal3) {C : ℝ}
    (hC : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖))
    (hInv : LInvBound) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10) (hfs : DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2 ∧
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
          Real.log ((q : ℝ) * (|s.im| + 2))) := by
  set z₀ : ℂ := (21 / 20 : ℂ) + s.im * I with hz₀
  have hz₀re : z₀.re = 21 / 20 := by simp [hz₀]
  set A : ℝ := 21 * (|C| + 1) with hAdef
  have hq1 := one_le_modulus_real q
  have hX : (0 : ℝ) < (q : ℝ) * (|s.im| + 2) := by positivity
  set M : ℝ := 2 * A * ((q : ℝ) * (|s.im| + 2)) with hMdef
  have hA1 : 1 ≤ A := by
    have := abs_nonneg C
    rw [hAdef]
    nlinarith
  have hM1 : 1 ≤ M := by
    have h2 : 2 ≤ (q : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
    rw [hMdef]
    nlinarith
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hz₀re]; norm_num)
  have hinv := hInv q χ z₀ (by rw [hz₀re]; norm_num)
  rw [hz₀re] at hinv
  have h21 : ‖DirichletCharacter.LFunction χ z₀‖⁻¹ ≤ 21 := by
    have e : (21 / 20 : ℝ) / (21 / 20 - 1) = 21 := by norm_num
    linarith
  have hlow : 1 ≤ 21 * ‖DirichletCharacter.LFunction χ z₀‖ := by
    have hp : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    have := mul_le_mul_of_nonneg_right h21 hp.le
    rwa [inv_mul_cancel₀ hp.ne'] at this
  have hbound : ∀ z ∈ Metric.closedBall z₀ (11 / 20),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre := re_ge_of_mem_closedBall hz
    rw [hz₀re] at hre
    have h1 := hC q χ hχ z (by linarith)
    have hn := norm_le_norm_add_of_mem_closedBall' hz
    have hn0 := norm_disc_center_le s.im
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hz1 : 1 + ‖z‖ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
    have hY : 0 ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by positivity
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ |C| * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hq0)
            (by positivity)
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hq0) hz1 (by positivity)
          positivity
      _ = (|C| + 1) * q * (2 * (|s.im| + 2)) * 1 := by ring
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) * (21 * ‖DirichletCharacter.LFunction χ z₀‖) :=
          mul_le_mul_of_nonneg_left hlow hY
      _ = M * ‖DirichletCharacter.LFunction χ z₀‖ := by
          rw [hMdef, hAdef]
          ring
  obtain ⟨Z, m, hZ, -, -, hm1, hsum, hder⟩ := hLL (DirichletCharacter.LFunction χ) z₀ (11 / 20) M
    (by norm_num) hM1 (DirichletCharacter.differentiable_LFunction hχ).differentiableOn hf0 hbound
  have hlogM : Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * Real.log ((q : ℝ) * (|s.im| + 2)) :=
    log_le_of_le_exp_log_conductor hA1 hM1 (log_two_le_log_analytic_conductor q s.im) (Real.exp_pos _)
      (by rw [Real.exp_log hX, hMdef])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Z, m, hZ, hm1, ?_, ?_⟩
  · push_cast at hsum
    calc ∑ ρ ∈ Z, (m ρ : ℝ) ≤ Real.log M / Real.log 2 := hsum
      _ ≤ _ := div_le_div_of_nonneg_right hlogM hl2.le
  · have hs6 : s ∈ Metric.closedBall z₀ (11 / 20 / 6) := by
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have e : s - z₀ = ((s.re - 21 / 20 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hz₀]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ ≤ 72 * Real.log M / (11 / 20) := hder s hs6 hfs
      _ = 1440 / 11 * Real.log M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogM (by norm_num)

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogDerivSubExceptionalZeros
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma log_deriv_sub_exceptional_zeros {c₁ : ℝ} (hc₁ : 0 < c₁) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {B : Finset ℝ} (hχ : χ ≠ 1) (hBcard : B.card ≤ 1)
    (hBmem : ∀ β ∈ B, χ ≠ 1 ∧ InRegion c₁ q (β : ℂ) ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
      deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0)
    (hBall : ∀ s : ℂ, InRegion c₁ q s → IsLZero χ s → ∃ β ∈ B, s = (β : ℂ))
    {s : ℂ} (hs : InRegion (c₁ / 2) q s) (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10)
    {Z : Finset ℂ} {m : ℂ → ℕ}
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0))
    (hm3 : ∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1)
    {K : ℝ}
    (hsum : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ K * Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2)
    (hE : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ 1440 / 11 * (K * Real.log ((q : ℝ) * (|s.im| + 2)))) :
    ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤
      1440 / 11 * (K * Real.log ((q : ℝ) * (|s.im| + 2))) +
      3 * K / (c₁ * Real.log 2) * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 + 120 / 11 := by
  have hs' : 1 - c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog2 : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set L := Real.log ((q : ℝ) * (|s.im| + 2)) with hLdef
  have hL2 : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := hLpos.ne'
  have hfar : ∀ ρ ∈ Z, (∀ β ∈ B, ρ ≠ (β : ℂ)) → ‖1 / (s - ρ)‖ ≤ 3 * L / c₁ := by
    intro ρ hρ hne
    obtain ⟨hball, hzero⟩ := (hZ ρ).mp hρ
    have hnot : ¬ InRegion c₁ q ρ := by
      intro hreg
      obtain ⟨β, hβ, hρβ⟩ := hBall ρ hreg ⟨Or.inl hχ, hzero⟩
      exact hne β hβ hρβ
    simp only [InRegion, not_le] at hnot
    have him : |ρ.im - s.im| ≤ 11 / 60 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      have h1 := Complex.abs_im_le_norm (ρ - ((21 / 20 : ℂ) + s.im * I))
      have hime : (ρ - ((21 / 20 : ℂ) + s.im * I)).im = ρ.im - s.im := by simp
      rw [hime] at h1
      linarith
    set Lρ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLρdef
    have hLρ2 : Real.log 2 ≤ Lρ :=
      Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
    have hLρpos : 0 < Lρ := by linarith
    have hLρ : Lρ ≤ 6 / 5 * L := by
      have h1 : (q : ℝ) * (|ρ.im| + 2) ≤ (q : ℝ) * (|s.im| + 2) * (131 / 120) := by
        have h0 : |ρ.im| ≤ |s.im| + 11 / 60 := by
          have := abs_sub_abs_le_abs_sub ρ.im s.im
          linarith
        nlinarith [abs_nonneg s.im]
      have h2 : Lρ ≤ L + Real.log (131 / 120) := by
        rw [hLρdef, hLdef, ← Real.log_mul (by positivity) (by norm_num)]
        exact Real.log_le_log (by positivity) h1
      have h3 : Real.log (131 / 120) ≤ 131 / 120 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    have h1 : c₁ / (6 / 5 * L) ≤ c₁ / Lρ := div_le_div_of_nonneg_left hc₁.le hLρpos hLρ
    have h1' : c₁ / (6 / 5 * L) = 5 * c₁ / (6 * L) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    have h2 : c₁ / (3 * L) = 5 * c₁ / (6 * L) - c₁ / 2 / L := by
      field_simp
      ring
    have hre : c₁ / (3 * L) ≤ (s - ρ).re := by
      rw [Complex.sub_re]
      linarith
    have hpos : 0 < c₁ / (3 * L) := div_pos hc₁ (by linarith)
    have hnorm : c₁ / (3 * L) ≤ ‖s - ρ‖ := hre.trans (Complex.re_le_norm _)
    rw [norm_div, norm_one]
    calc 1 / ‖s - ρ‖ ≤ 1 / (c₁ / (3 * L)) := one_div_le_one_div_of_le hpos hnorm
      _ = 3 * L / c₁ := by rw [one_div_div]
  have hnear : ∀ β ∈ B, (β : ℂ) ∉ Z → ‖1 / (s - (β : ℂ))‖ ≤ 120 / 11 := by
    intro β hβ hβZ
    have hout : ¬ (β : ℂ) ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) := by
      intro hin
      exact hβZ ((hZ _).mpr ⟨hin, (hBmem β hβ).2.2.1⟩)
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hout
    have hsc : ‖s - ((21 / 20 : ℂ) + s.im * I)‖ ≤ 47 / 540 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have hre' : (s - ((21 / 20 : ℂ) + s.im * I)).re = s.re - 21 / 20 := by simp
      have him' : (s - ((21 / 20 : ℂ) + s.im * I)).im = 0 := by simp
      rw [hre', him', abs_zero, add_zero, abs_le]
      constructor <;> linarith
    have htri := norm_sub_le_norm_sub_add_norm_sub (β : ℂ) s ((21 / 20 : ℂ) + s.im * I)
    rw [norm_sub_rev (β : ℂ) s] at htri
    have hd : (11 : ℝ) / 120 ≤ ‖s - (β : ℂ)‖ := by linarith
    rw [norm_div, norm_one]
    calc 1 / ‖s - (β : ℂ)‖ ≤ 1 / (11 / 120) := one_div_le_one_div_of_le (by norm_num) hd
      _ = 120 / 11 := by norm_num
  have hmsum : ∀ Z' ⊆ Z, (∀ ρ ∈ Z', ∀ β ∈ B, ρ ≠ (β : ℂ)) →
      ‖∑ ρ ∈ Z', (m ρ : ℂ) / (s - ρ)‖ ≤ 3 * K / (c₁ * Real.log 2) * L ^ 2 := by
    intro Z' hZ' hne
    have hc3 : 0 ≤ 3 * L / c₁ := div_nonneg (by linarith) hc₁.le
    calc ‖∑ ρ ∈ Z', (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z', ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z', (m ρ : ℝ) * (3 * L / c₁) := Finset.sum_le_sum fun ρ hρ => by
          rw [div_eq_mul_one_div, norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (hfar ρ (hZ' hρ) (hne ρ hρ)) (Nat.cast_nonneg _)
      _ = (∑ ρ ∈ Z', (m ρ : ℝ)) * (3 * L / c₁) := by rw [Finset.sum_mul]
      _ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (3 * L / c₁) :=
          mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum_of_subset_of_nonneg hZ' fun _ _ _ => Nat.cast_nonneg _) hc3
      _ ≤ K * L / Real.log 2 * (3 * L / c₁) := mul_le_mul_of_nonneg_right hsum hc3
      _ = 3 * K / (c₁ * Real.log 2) * L ^ 2 := by ring
  have hdecomp : negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ)) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) +
        ((∑ β ∈ B, 1 / (s - (β : ℂ))) - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) := by
    unfold negLD
    ring
  have hdiff : ‖(∑ β ∈ B, 1 / (s - (β : ℂ))) - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
      3 * K / (c₁ * Real.log 2) * L ^ 2 + 120 / 11 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hBcard with h0 | h1
    · obtain rfl := Finset.card_eq_zero.mp h0
      rw [Finset.sum_empty, zero_sub, norm_neg]
      have h2 := hmsum Z subset_rfl (fun ρ _ β hβ => by simp at hβ)
      linarith
    · obtain ⟨β, rfl⟩ := Finset.card_eq_one.mp h1
      rw [Finset.sum_singleton]
      by_cases hβZ : (β : ℂ) ∈ Z
      · rw [← Finset.add_sum_erase Z _ hβZ,
          hm3 _ hβZ (hBmem β (Finset.mem_singleton_self β)).2.2.2, Nat.cast_one,
          sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
        have h2 := hmsum (Z.erase (β : ℂ)) (Finset.erase_subset _ _) (fun ρ hρ β' hβ' => by
          rw [Finset.mem_singleton] at hβ'
          subst hβ'
          exact Finset.ne_of_mem_erase hρ)
        linarith
      · refine (norm_sub_le _ _).trans ?_
        have h2 := hnear β (Finset.mem_singleton_self β) hβZ
        have h3 := hmsum Z subset_rfl (fun ρ hρ β' hβ' => by
          rw [Finset.mem_singleton] at hβ'
          subst hβ'
          exact fun h => hβZ (h ▸ hρ))
        linarith
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith [hE, hdiff]

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaNegReal
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma exponential_integral_nonneg_real {σ a : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    ∃ r : ℝ, 0 ≤ r ∧ Formalism.ZF.ComplexPowerDifferenceIntegral.eint (σ : ℂ) a = (r : ℂ) := by
  refine ⟨∫ x in a..(a + 1), (x ^ (-σ) - (a + 1) ^ (-σ)), ?_, ?_⟩
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 := Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith : -σ ≤ 0)
    linarith
  · unfold Formalism.ZF.ComplexPowerDifferenceIntegral.eint
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 ≤ x := le_trans ha.le hx.1
    simp only [Complex.ofReal_sub]
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ a + 1)]
    push_cast
    ring

theorem zeta_negative_real_axis : ZetaNegReal := by
  intro σ hσ0 hσ1
  have hre : 0 < (σ : ℂ).re := by simpa using hσ0
  have hz1 := Formalism.ZF.ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hre
  have hne : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hζ := riemannZeta_eq_inv_sub_mul hne
  choose r hr0 hr using fun n : ℕ =>
    exponential_integral_nonneg_real (σ := σ) (a := (n : ℝ) + 1) hσ0.le (by positivity)
  have hdz : ∀ n : ℕ, Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n = ((σ : ℂ) - 1) * ((r n : ℝ) : ℂ) := by
    intro n
    rw [← hr n]
    exact Formalism.ZF.ComplexPowerDifferenceIntegral.d_eq (by positivity) _
  have hsum : Summable r := by
    have hs := Formalism.ZF.ComplexPowerDifferenceIntegral.summable_norm_dz hre
    have hs' : Summable (fun n => ‖((σ : ℂ) - 1)‖⁻¹ * ‖Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n‖) := hs.mul_left _
    refine hs'.congr (fun n => ?_)
    rw [hdz n, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne'), one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
  have hDz : Formalism.ZF.ComplexPowerDifferenceIntegral.Dz (σ : ℂ) = ((σ : ℂ) - 1) * ((∑' n, r n : ℝ) : ℂ) := by
    unfold Formalism.ZF.ComplexPowerDifferenceIntegral.Dz
    simp_rw [hdz]
    rw [tsum_mul_left, Complex.ofReal_tsum]
  set R := ∑' n, r n with hRdef
  have hR0 : 0 ≤ R := tsum_nonneg hr0
  have hval : riemannZeta (σ : ℂ) = ((σ / (σ - 1) - R : ℝ) : ℂ) := by
    rw [hζ, hz1, hDz]
    have hσ1' : (σ - 1 : ℝ) ≠ 0 := by intro h; linarith
    push_cast
    field_simp
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  have : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg hσ0 (by linarith)
  linarith

end Formalism.ZeroFreeDirichlet
end
end

