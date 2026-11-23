module

public import Mathlib

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

theorem log_add_log_two_pi_le : log 280 + log (2 * π) ≤ 7.6 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_gt_three
  rw [← Real.log_mul (by norm_num) (by positivity)]
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hsplit : exp 7.6 = exp 1 ^ 7 * exp 0.6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  have h7 : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 7
  have h06 : (1 + 0.6 + 0.6 ^ 2 / 2 : ℝ) ≤ exp 0.6 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hpos : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7 := by positivity
  calc 280 * (2 * π) ≤ (2.7182818283 : ℝ) ^ 7 * (1 + 0.6 + 0.6 ^ 2 / 2) := by
        norm_num; nlinarith
    _ ≤ exp 1 ^ 7 * exp 0.6 :=
        mul_le_mul h7 h06 (by norm_num) (by positivity)

theorem log_two_pi_le : log (2 * π) ≤ 7.6 := by
  have h := log_add_log_two_pi_le
  have h280 : 0 ≤ log (280 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

end GroundTheory.Heights₂.Heights
