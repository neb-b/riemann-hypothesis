module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.AbsZeroTermSecondDifferenceLe
section
noncomputable section

namespace Formalism.ZeroFreeDirichlet

private theorem one_add_rpow_le_one_add_mul {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 + s) ^ p ≤ 1 + p * s := by
  have t := Real.geom_mean_le_arith_mean2_weighted hp0 (sub_nonneg.2 hp1)
    (by linarith : (0:ℝ) ≤ 1 + s) zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at t
  nlinarith [t]

private theorem le_one_add_mul_log_one_add {h : ℝ} (hh : 0 ≤ h) : h ≤ (1 + h) * Real.log (1 + h) := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have t := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at t
  have e : (1 + h) * (1 + h)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  nlinarith [mul_le_mul_of_nonneg_left t h1.le]

lemma abs_zero_term_second_difference_le {y h β : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (_hh1 : h ≤ 1) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β < 1) :
    |(y * (1 + h)) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
        + y * h * (y ^ β / β)| ≤ 2 * y ^ 2 * h ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hβ0 : 0 < β := by linarith
  have hq : 0 < 1 - β := by linarith
  have hβne : β ≠ 0 := hβ0.ne'
  have hβ1ne : β - 1 ≠ 0 := by linarith
  have hq1ne : 1 - β ≠ 0 := hq.ne'
  have hmul : (y * (1 + h)) ^ β = y ^ β * (1 + h) ^ β := Real.mul_rpow hy0 h1.le
  have hAq : (1 + h) ^ β * (1 + h) ^ (1 - β) = 1 + h := by
    have e : β + (1 - β) = 1 := by ring
    rw [← Real.rpow_add h1, e, Real.rpow_one]
  have hBern : (1 + h) ^ (1 - β) ≤ 1 + (1 - β) * h :=
    one_add_rpow_le_one_add_mul hh.le hq.le (by linarith)
  have hD0 : (1 + h) ^ β ≤ 1 + β * h := one_add_rpow_le_one_add_mul hh.le hβ0.le hβ2.le
  have hA0 : 0 ≤ (1 + h) ^ β := Real.rpow_nonneg h1.le _
  have hB0 : 0 ≤ y ^ β := Real.rpow_nonneg hy0 _
  have hBy : y ^ β ≤ y := by
    have t := Real.rpow_le_rpow_of_exponent_le hy hβ2.le
    rwa [Real.rpow_one] at t
  set A := (1 + h) ^ β with hA
  set B := y ^ β with hB
  have hD1 : (1 + β * h - A) * (1 + (1 - β) * h) ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hBern hA0]
  have hD2 : 1 + β * h - A ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hD0) (mul_nonneg hq.le hh.le)]
  have key : (y * (1 + h)) * (B / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
      + y * h * (B / β) = -(y * B * ((1 + β * h - A) / (β * (1 - β)))) := by
    rw [hmul]
    field_simp
    ring
  rw [key, abs_neg]
  have hpos : 0 < β * (1 - β) := mul_pos hβ0 hq
  have hE0 : 0 ≤ (1 + β * h - A) / (β * (1 - β)) := div_nonneg (by linarith) hpos.le
  have hE : (1 + β * h - A) / (β * (1 - β)) ≤ h ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hy0 hB0) hE0)]
  have s1 : y * B * ((1 + β * h - A) / (β * (1 - β))) ≤ y * B * h ^ 2 :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg hy0 hB0)
  have s2 : y * B * h ^ 2 ≤ y * y * h ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBy hy0) (sq_nonneg h)
  nlinarith [mul_nonneg (sq_nonneg y) (sq_nonneg h)]

lemma abs_main_term_second_difference_le {y h γ : ℝ} (hy : 0 < y) (hh : 0 < h) :
    |y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y| ≤ y ^ 2 * h ^ 2 := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hlog : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) :=
    Real.log_mul hy.ne' h1.ne'
  have key : y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y
      = y ^ 2 * ((1 + h) * Real.log (1 + h) - h) := by
    rw [hlog]; ring
  rw [key]
  have hL1 : Real.log (1 + h) ≤ h := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hL2 := le_one_add_mul_log_one_add hh.le
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg y) (by linarith))]
  have t : (1 + h) * Real.log (1 + h) - h ≤ h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 h1.le]
  nlinarith [mul_le_mul_of_nonneg_left t (sq_nonneg y)]

lemma exp_neg_sqrt_log_le_sq {cs c₀ y z : ℝ} (hc0 : 0 ≤ c₀) (hcs : c₀ ≤ cs) (hy : 1 ≤ y) (hyz : y ≤ z) :
    Real.exp (-cs * Real.sqrt (Real.log z)) ≤ Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ^ 2 := by
  have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz
  have hs : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log z) := Real.sqrt_le_sqrt hlyz
  rw [sq, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul hcs hs (Real.sqrt_nonneg _) (le_trans hc0 hcs)]

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LeOfSecondDifferenceBound
section
noncomputable section

namespace Formalism.ZeroFreeDirichlet


set_option maxHeartbeats 800000 in
lemma le_of_second_difference_bound {y c₀ C N eY ey h : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hC : 0 ≤ C)
    (hh : h = Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)))
    (hey0 : 0 ≤ ey) (heY0 : 0 ≤ eY) (hey : ey ≤ h ^ 2) (heY : eY ≤ h ^ 2)
    (hmain : y * h * N ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (C * (y * (1 + h)) * eY) + y * (1 + h) * (C * y * ey)) :
    N ≤ (128 / c₀ ^ 2 + 2 + 4 * C) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hc2 : c₀ ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc01
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hlogmul : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) := by
    have hh0' : 0 < h := by rw [hh]; exact Real.exp_pos _
    exact Real.log_mul hy0.ne' (by linarith)
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  set g := Real.exp (-(c₀ / 4) * s) with hgdef
  have hg0 : 0 < g := Real.exp_pos _
  have hg1 : g ≤ 1 := by
    rw [hgdef, Real.exp_le_one_iff]
    have : 0 ≤ c₀ / 4 * s := by positivity
    linarith
  have hhg : h = g * g := by
    rw [hh, hgdef, ← Real.exp_add]; congr 1; ring
  have hh0 : 0 < h := by rw [hhg]; positivity
  have hhle : h ≤ g := by rw [hhg]; exact mul_le_of_le_one_left hg0.le hg1
  have hh1 : h ≤ 1 := le_trans hhle hg1
  have hyg : Real.exp (s ^ 2 / 2) ≤ y * g := by
    have hyL : y = Real.exp L := (Real.exp_log hy0).symm
    rw [hgdef, hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hB : L + 1 ≤ 2 * (y * g) := by
    have : 0 ≤ (s ^ 2 / 2) ^ 2 / 2 := by positivity
    linarith
  have ht := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ c₀ / 4 * s by positivity)
  have hgt : g * Real.exp (c₀ / 4 * s) = 1 := by
    rw [hgdef, ← Real.exp_add, show -(c₀ / 4) * s + c₀ / 4 * s = 0 by ring, Real.exp_zero]
  have hA1 : g * (c₀ / 4 * s) ^ 2 ≤ 2 := by
    have h0 : 0 ≤ c₀ / 4 * s := by positivity
    have : (c₀ / 4 * s) ^ 2 ≤ 2 * Real.exp (c₀ / 4 * s) := by linarith
    calc g * (c₀ / 4 * s) ^ 2 ≤ g * (2 * Real.exp (c₀ / 4 * s)) :=
          mul_le_mul_of_nonneg_left this hg0.le
      _ = 2 * (g * Real.exp (c₀ / 4 * s)) := by ring
      _ = 2 := by rw [hgt]; ring
  have hA : c₀ ^ 2 * g * (L + 1) ≤ 33 := by
    have e : c₀ ^ 2 * g * (L + 1) = 16 * (g * (c₀ / 4 * s) ^ 2) + c₀ ^ 2 * g := by
      rw [← hss]; ring
    have : c₀ ^ 2 * g ≤ 1 := mul_le_one₀ hc2 hg0.le hg1
    rw [e]; linarith
  have hA' : g * (L + 1) ≤ 33 / c₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have e : g * (L + 1) * c₀ ^ 2 = c₀ ^ 2 * g * (L + 1) := by ring
    rw [e]; exact hA
  have hlog : Real.log (y * (1 + h)) ≤ L + 1 := by
    rw [hlogmul]
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + h)
    linarith
  have hP : 0 < y * h := by positivity
  have hyh1 : y * (1 + h) - y = y * h := by ring
  rw [hyh1] at hmain
  have T1 : (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h) * ((y * h + 1) * (L + 1)) := by
    have : (y * h) * Real.log (y * (1 + h)) ≤ (y * h) * (L + 1) :=
      mul_le_mul_of_nonneg_left hlog hP.le
    calc (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h + 1) * ((y * h) * (L + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (y * h) * ((y * h + 1) * (L + 1)) := by ring
  have T1' : (y * h + 1) * (L + 1) ≤ (33 / c₀ ^ 2 + 2) * (y * g) := by
    calc (y * h + 1) * (L + 1) = (y * g) * (g * (L + 1)) + (L + 1) := by rw [hhg]; ring
      _ ≤ (y * g) * (33 / c₀ ^ 2) + 2 * (y * g) :=
          add_le_add (mul_le_mul_of_nonneg_left hA' (by positivity)) hB
      _ = (33 / c₀ ^ 2 + 2) * (y * g) := by ring
  have T2 : 2 * y ^ 2 * h ^ 2 ≤ (y * h) * (2 * (y * g)) := by
    have : y * h ≤ y * g := mul_le_mul_of_nonneg_left hhle hy0.le
    calc 2 * y ^ 2 * h ^ 2 = (y * h) * (2 * (y * h)) := by ring
      _ ≤ (y * h) * (2 * (y * g)) := mul_le_mul_of_nonneg_left (by linarith) hP.le
  have hhh : (1 + h) * h ≤ 2 * g := by
    have h1 : h * h ≤ h := mul_le_of_le_one_left hh0.le hh1
    have e : (1 + h) * h = h + h * h := by ring
    rw [e]; linarith
  have hCy : 0 ≤ C * y := mul_nonneg hC hy0.le
  have T3 : y * (C * (y * (1 + h)) * eY) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ C * (y * (1 + h)) := mul_nonneg hC (by positivity)
    have : C * (y * (1 + h)) * eY ≤ C * (y * (1 + h)) * h ^ 2 := mul_le_mul_of_nonneg_left heY hk
    calc y * (C * (y * (1 + h)) * eY) ≤ y * (C * (y * (1 + h)) * h ^ 2) :=
          mul_le_mul_of_nonneg_left this hy0.le
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T4 : y * (1 + h) * (C * y * ey) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ y * (1 + h) * (C * y) := mul_nonneg (by positivity) hCy
    have : y * (1 + h) * (C * y) * ey ≤ y * (1 + h) * (C * y) * h ^ 2 :=
      mul_le_mul_of_nonneg_left hey hk
    calc y * (1 + h) * (C * y * ey) = y * (1 + h) * (C * y) * ey := by ring
      _ ≤ y * (1 + h) * (C * y) * h ^ 2 := this
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T1'' := mul_le_mul_of_nonneg_left T1' hP.le
  have hfin : (33 / c₀ ^ 2 + 2) * (y * g) + 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) ≤
      (128 / c₀ ^ 2 + 2 + 4 * C) * y * g := by
    have h95 : 2 ≤ 95 / c₀ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have := mul_le_mul_of_nonneg_right h95 (by positivity : (0 : ℝ) ≤ y * g)
    have e1 : (128 / c₀ ^ 2 + 2 + 4 * C) * y * g =
        (33 / c₀ ^ 2 + 2) * (y * g) + 95 / c₀ ^ 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) := by
      ring
    rw [e1]; linarith
  have hfin' := mul_le_mul_of_nonneg_left hfin hP.le
  refine le_of_mul_le_mul_left ?_ hP
  linarith

lemma mul_le_of_log_bounds {y c₀ K lq : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hK : K * Real.log 2 ≤ Real.log y) (hK0 : 0 ≤ K) (hlq0 : 0 ≤ lq)
    (hlq : lq ≤ c₀ / 4 * Real.sqrt (Real.log y)) :
    K * lq ≤ 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hyL : y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  have hKL : K ≤ 2 * L := by nlinarith
  have hlq' : lq ≤ s / 4 := by
    have : c₀ / 4 * s ≤ 1 / 4 * s := mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  have hKlq : K * lq ≤ (2 * L) * (s / 4) := mul_le_mul hKL hlq' hlq0 (by positivity)
  have hexp : Real.exp (s ^ 2 / 2) ≤ y * Real.exp (-(c₀ / 4) * s) := by
    rw [hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hpoly : (2 * L) * (s / 4) ≤ 16 * (1 + s ^ 2 / 2 + (s ^ 2 / 2) ^ 2 / 2) := by
    rw [← hss]; nlinarith [sq_nonneg (s ^ 2 - s), sq_nonneg s]
  have e : 16 * y * Real.exp (-(c₀ / 4) * s) = 16 * (y * Real.exp (-(c₀ / 4) * s)) := by ring
  rw [e]
  linarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SumVonMangoldtNotCoprimeLe
section
open Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def weightedPartialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n * ((x / n - 1 : ℝ) : ℂ)

def partialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n

lemma sum_Icc_eq_add_sum_Ioc (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]

lemma weightedSum_identity (f : ℕ → ℂ) {y Y : ℝ} (hyY : y ≤ Y) :
    (y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y
      = ((Y - y : ℝ) : ℂ) * partialSumUpTo f y
        + ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ) := by
  unfold weightedPartialSumUpTo partialSumUpTo
  rw [sum_Icc_eq_add_sum_Ioc _ (Nat.floor_mono hyY)]
  simp only [mul_add, Finset.mul_sum]
  rw [show ∀ a b c : ℂ, a + b - c = (a - c) + b from fun a b c => by ring, ← Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring

lemma norm_sum_Ioc_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  have hY1 : 1 ≤ Y := le_trans hy hyY
  have hterm : ∀ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊,
      ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ ≤ (Y - y) * Real.log Y := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : y < (n : ℝ) := by
      have := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      linarith
    have hn2 : (n : ℝ) ≤ Y := by
      have := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 : (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn.2
      linarith
    have hnpos : (0:ℝ) < n := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA : 0 ≤ y * (Y / n - 1) := by
      apply mul_nonneg (by linarith)
      rw [sub_nonneg, le_div_iff₀ hnpos]; linarith
    have hB : y * (Y / n - 1) ≤ Y - y := by
      have e : y * (Y / n - 1) = (Y - n) * (y / n) := by field_simp
      rw [e]
      have h3 : y / n ≤ 1 := by rw [div_le_one hnpos]; linarith
      have h4 : 0 ≤ Y - n := by linarith
      nlinarith
    rw [abs_of_nonneg hA]
    have hf' : ‖f n‖ ≤ Real.log Y :=
      calc ‖f n‖ ≤ Λ n := hf n
        _ ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log Y := Real.log_le_log hnpos hn2
    calc ‖f n‖ * (y * (Y / n - 1)) ≤ Real.log Y * (Y - y) :=
          mul_le_mul hf' hB hA (Real.log_nonneg hY1)
      _ = (Y - y) * Real.log Y := by ring
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, (Y - y) * Real.log Y := Finset.sum_le_sum hterm
    _ = ((Ioc ⌊y⌋₊ ⌊Y⌋₊).card : ℝ) * ((Y - y) * Real.log Y) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (Real.log_nonneg hY1))
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hyY)]
      have h1 := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 := Nat.lt_floor_add_one y
      linarith

lemma norm_weightedSum_sub_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖((y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y) - ((Y - y : ℝ) : ℂ) * partialSumUpTo f y‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  rw [weightedSum_identity f hyY, add_sub_cancel_left]
  exact norm_sum_Ioc_le f hf hy hyY

lemma sum_vonMangoldt_not_coprime_le (q : ℕ) (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n * (if n.Coprime q then 0 else 1) ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  set K := Nat.log 2 N
  set g : ℕ → ℝ := fun n => Λ n * (if n.Coprime q then 0 else 1) with hg
  have hgle : ∀ n, g n ≤ Λ n := fun n => by
    simp only [hg]; split_ifs <;> simp [vonMangoldt_nonneg]
  have hsub : (Icc 1 N).filter (fun n => g n ≠ 0) ⊆ (q ^ K).divisors := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hN⟩, hgn⟩ := hn
    have hΛ : Λ n ≠ 0 := by intro h; apply hgn; simp [hg, h]
    have hnc : ¬ n.Coprime q := by intro h; apply hgn; simp [hg, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hpq : p ∣ q := by
      by_contra hc
      exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))
    have hkK : k ≤ K := by
      apply Nat.le_log_of_pow_le one_lt_two
      exact le_trans (Nat.pow_le_pow_left hp.two_le k) hN
    rw [Nat.mem_divisors]
    exact ⟨(pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK), pow_ne_zero _ hq⟩
  calc ∑ n ∈ Icc 1 N, g n = ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), g n :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), Λ n := Finset.sum_le_sum fun n _ => hgle n
    _ ≤ ∑ n ∈ (q ^ K).divisors, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = (K : ℝ) * Real.log q := by rw [vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

lemma one_apply_natCast {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if n.Coprime q then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 h)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).1 hu))

end Formalism.ZeroFreeDirichlet
end
end

