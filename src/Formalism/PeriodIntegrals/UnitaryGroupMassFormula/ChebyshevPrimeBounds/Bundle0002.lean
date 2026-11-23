module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialEqSumOfLe
section
noncomputable section

namespace PI.PC

open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta

theorem log_factorial_eq_sum_log (N : ℕ) : log ((N ! : ℕ) : ℝ) = ∑ m ∈ Ioc 0 N, log (m : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    push_cast
    ring

theorem log_factorial_eq_sum (N : ℕ) :
    log ((N ! : ℕ) : ℝ) = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have h1 : ∀ m ∈ Ioc 0 N, log (m : ℝ) = ∑ d ∈ Ioc 0 N, if d ∣ m then Λ d else 0 := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [← Finset.sum_filter, ← ArithmeticFunction.vonMangoldt_sum]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm.1, (Nat.le_of_dvd hm.1 hd).trans hm.2⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
  ring

theorem log_factorial_eq_sum_of_le {N M : ℕ} (h : N ≤ M) :
    log ((N ! : ℕ) : ℝ) = ∑ d ∈ Ioc 0 M, Λ d * ((N / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum]
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right h)
  intro d hdM hd
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hdM).1
  have hNd : N < d := by
    by_contra hc
    exact hd (Finset.mem_Ioc.mpr ⟨hd0, by omega⟩)
  rw [Nat.div_eq_of_lt hNd]
  simp

def chE (q : ℕ) : ℝ :=
  (q : ℝ) - ((q / 2 : ℕ) : ℝ) - ((q / 3 : ℕ) : ℝ) - ((q / 5 : ℕ) : ℝ) + ((q / 30 : ℕ) : ℝ)

theorem chE_nonneg (q : ℕ) : 0 ≤ chE q := by
  have h : q / 2 + q / 3 + q / 5 ≤ q + q / 30 := by omega
  have h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) ≤ (q : ℝ) + ((q / 30 : ℕ) : ℝ) := by
    exact_mod_cast h
  unfold chE
  linarith

theorem chE_le_one (q : ℕ) : chE q ≤ 1 := by
  have h : q + q / 30 ≤ q / 2 + q / 3 + q / 5 + 1 := by omega
  have h' : (q : ℝ) + ((q / 30 : ℕ) : ℝ) ≤ ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) + 1 := by
    exact_mod_cast h
  unfold chE
  linarith

theorem chE_eq_one {q : ℕ} (h1 : 1 ≤ q) (h6 : q < 6) : chE q = 1 := by
  have h : q / 2 + q / 3 + q / 5 + 1 = q + q / 30 := by omega
  have h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) + 1 = (q : ℝ) + ((q / 30 : ℕ) : ℝ) := by
    exact_mod_cast h
  unfold chE
  linarith

private theorem nat_floor_div_natCast (x : ℝ) (k : ℕ) : ⌊x / (k : ℝ)⌋₊ = ⌊x⌋₊ / k :=
  Nat.floor_div_natCast x k

theorem chD_eq_sum (x : ℝ) : chD x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d) := by
  have hL : ∀ k : ℕ, lf (x / (k : ℝ)) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (((⌊x⌋₊ / d) / k : ℕ) : ℝ) := by
    intro k
    unfold lf
    rw [nat_floor_div_natCast, log_factorial_eq_sum_of_le (Nat.div_le_self ⌊x⌋₊ k)]
    apply Finset.sum_congr rfl
    intro d _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]
  have h1 : lf x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ((⌊x⌋₊ / d : ℕ) : ℝ) := by
    unfold lf
    exact log_factorial_eq_sum _
  have h2 := hL 2
  have h3 := hL 3
  have h5 := hL 5
  have h30 := hL 30
  push_cast at h2 h3 h5 h30
  unfold chD
  rw [h1, h2, h3, h5, h30]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold chE
  ring

private theorem chebyshev_psi_eq_sum_Ioc_vonMangoldt (x : ℝ) : ψ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n := by
  rfl

theorem chD_le_psi (x : ℝ) : chD x ≤ ψ x := by
  rw [chD_eq_sum, chebyshev_psi_eq_sum_Ioc_vonMangoldt]
  apply Finset.sum_le_sum
  intro d _
  have hc := chE_le_one (⌊x⌋₊ / d)
  have h0 : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  exact mul_le_of_le_one_right h0 hc

private theorem sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc (N : ℕ) (f : ℕ → ℝ) :
    ∑ d ∈ Ioc 0 N, f d = ∑ d ∈ Ioc 0 (N / 6), f d + ∑ d ∈ Ioc (N / 6) N, f d := by
  rw [Finset.sum_Ioc_consecutive f (Nat.zero_le (N / 6)) (Nat.div_le_self N 6)]

theorem psi_sub_psi_le_chD (x : ℝ) : ψ x - ψ (x / 6) ≤ chD x := by
  have h6 : ⌊x / 6⌋₊ = ⌊x⌋₊ / 6 := by
    simpa using nat_floor_div_natCast x 6
  rw [chebyshev_psi_eq_sum_Ioc_vonMangoldt, chebyshev_psi_eq_sum_Ioc_vonMangoldt, h6, chD_eq_sum,
    sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d),
    sum_Ioc_eq_sum_Ioc_div_six_add_sum_Ioc ⌊x⌋₊ (fun d => Λ d * chE (⌊x⌋₊ / d))]
  have hA : 0 ≤ ∑ d ∈ Ioc 0 (⌊x⌋₊ / 6), Λ d * chE (⌊x⌋₊ / d) :=
    Finset.sum_nonneg fun d _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (chE_nonneg _)
  have hB : ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d ≤
      ∑ d ∈ Ioc (⌊x⌋₊ / 6) ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd0 : 0 < d := by omega
    have hq1 : 1 ≤ ⌊x⌋₊ / d := Nat.div_pos hd.2 hd0
    have hq6 : ⌊x⌋₊ / d < 6 := by
      exact Nat.div_lt_of_lt_mul (by omega)
    rw [chE_eq_one hq1 hq6, mul_one]
  linarith

theorem sandwich : Sandwich := fun x _ => ⟨psi_sub_psi_le_chD x, chD_le_psi x⟩

end PI.PC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialLe
section
noncomputable section

namespace PI.PC

open Finset Real
open scoped Nat

theorem g_diff {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * log a ≤ (b * log b - b) - (a * log a - a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h
  have h2 : b - a ≤ b * (log b - log a) := by
    have h3 := mul_le_mul_of_nonneg_left h hb.le
    rwa [mul_sub, mul_one, mul_div_cancel₀ _ hb.ne'] at h3
  have e : (b * log b - b) - (a * log a - a) - (b - a) * log a = b * (log b - log a) - (b - a) := by
    ring
  linarith

theorem g_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : a * log a - a ≤ b * log b - b := by
  have h := g_diff (by linarith : (0 : ℝ) < a) hab
  have hl : 0 ≤ (b - a) * log a := mul_nonneg (by linarith) (Real.log_nonneg ha)
  linarith

theorem third_le_log : (1 : ℝ) / 3 ≤ log (3 / 2) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  calc (1 : ℝ) / 3 = 1 - (3 / 2)⁻¹ := by norm_num
    _ ≤ log (3 / 2) := h

theorem h_mono {a b : ℝ} (ha : 3 / 2 ≤ a) (hab : a ≤ b) :
    a * log a - a - log a / 2 ≤ b * log b - b - log b / 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hg := g_diff ha0 hab
  have hlog : log b - log a ≤ (b - a) / a := by
    have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    rwa [show b / a - 1 = (b - a) / a by field_simp] at h
  have hla : 1 / 3 ≤ log a := le_trans third_le_log (Real.log_le_log (by norm_num) ha)
  have h3 : (b - a) / a ≤ (b - a) * (2 / 3) := by
    rw [div_le_iff₀ ha0]
    nlinarith
  have h4 : (b - a) * (1 / 3) ≤ (b - a) * log a := mul_le_mul_of_nonneg_left hla (by linarith)
  linarith

theorem h_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 ≤ b) :
    a * log a - a - log a / 2 ≤ b * log b - b - log b / 2 := by
  by_cases ha' : 3 / 2 ≤ a
  · exact h_mono ha' hab
  push_neg at ha'
  have hb2 := h_mono (a := 2) (b := b) (by norm_num) hb
  have hla : log a ≤ a - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hq : (a - 1 / 2) * log a ≤ (a - 1 / 2) * (a - 1) :=
    mul_le_mul_of_nonneg_left hla (by linarith)
  have hq2 : (a - 1 / 2) * (a - 1) - a ≤ -1 := by nlinarith
  have h2 : -1 ≤ 2 * log 2 - 2 - log 2 / 2 := by
    have := Real.log_two_gt_d9
    linarith
  have e : (a - 1 / 2) * log a = a * log a - log a / 2 := by ring
  linarith

theorem log_factorial_le {n : ℕ} (hn : n ≠ 0) :
    log ((n ! : ℕ) : ℝ) ≤ n * log n - n + log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h1 : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have hpos := Stirling.stirlingSeq'_pos m
  have h2 := Real.log_le_log hpos h1
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at h2
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at h2
  push_cast at h2 ⊢
  nlinarith [h2]

theorem log_two_pi_ge : (9 : ℝ) / 5 ≤ log (2 * π) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  have h15 : (6 : ℝ) / 5 ≤ Real.exp (1 / 5) := by
    have := Real.add_one_le_exp (1 / 5 : ℝ)
    linarith
  have hsplit : Real.exp (9 / 5) * Real.exp (1 / 5) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have hpi := Real.pi_gt_d2
  have hpos : 0 < Real.exp (9 / 5) := Real.exp_pos _
  have he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_self_lt_mul_self (Real.exp_pos 1).le he
  have h3 : Real.exp (9 / 5) * (6 / 5) ≤ Real.exp (9 / 5) * Real.exp (1 / 5) :=
    mul_le_mul_of_nonneg_left h15 hpos.le
  nlinarith

theorem log_thirty_ge : (33 : ℝ) / 10 ≤ log 30 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he := Real.exp_one_lt_d9
  have hsplit : Real.exp (33 / 10) = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hm : Real.exp (3 / 10) * Real.exp (-3 / 10) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h1 : (7 : ℝ) / 10 ≤ Real.exp (-3 / 10) := by
    have := Real.add_one_le_exp (-3 / 10 : ℝ)
    linarith
  have h310 : Real.exp (3 / 10) ≤ 10 / 7 := by
    have hp := Real.exp_pos (3 / 10)
    nlinarith
  have he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_self_lt_mul_self (Real.exp_pos 1).le he
  have he3 : Real.exp 1 * Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 * 2.7182818286 :=
    mul_lt_mul'' he2 he (by positivity) (Real.exp_pos 1).le
  rw [hsplit]
  have h4 : Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) ≤
      (2.7182818286 * 2.7182818286 * 2.7182818286) * (10 / 7) :=
    mul_le_mul he3.le h310 (Real.exp_pos _).le (by norm_num)
  linarith

theorem lfUpper : LfUpper := by
  intro y hy
  simp only [lf]
  have hn1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hny : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have h := log_factorial_le (n := ⌊y⌋₊) (by omega)
  have hn1' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn1
  have hg := g_mono hn1' hny
  have hl := Real.log_le_log (by linarith) hny
  linarith

theorem lfLower : LfLower := by
  intro y hy
  simp only [lf]
  have hn1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hn1' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn1
  have hy' : y ≤ (⌊y⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one y).le
  have hS := Stirling.le_log_factorial_stirling (n := ⌊y⌋₊ + 1) (Nat.succ_ne_zero _)
  have hfac : Real.log (((⌊y⌋₊ + 1) ! : ℕ) : ℝ) =
      Real.log ((⌊y⌋₊ : ℝ) + 1) + Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have h2π := log_two_pi_ge
  have hh := h_le hy hy' (by linarith)
  push_cast at hS hfac
  linarith

theorem main_term {x : ℝ} (hx : 0 < x) :
    (x * log x - x) - (x / 2 * log (x / 2) - x / 2) - (x / 3 * log (x / 3) - x / 3)
      - (x / 5 * log (x / 5) - x / 5) + (x / 30 * log (x / 30) - x / 30) = chA * x := by
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx.ne' (by norm_num)
  rw [h2, h3, h5, h30]
  simp only [chA]
  ring

theorem stir_log_thirty : log 30 = log 2 + log 3 + log 5 := by
  rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

theorem dUpper : DUpper := by
  intro x hx
  simp only [chD]
  have hx0 : (0 : ℝ) < x := by linarith
  have l1 := lfUpper x (by linarith)
  have l30 := lfUpper (x / 30) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u2 := lfLower (x / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u3 := lfLower (x / 3) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u5 := lfLower (x / 5) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hm := main_term hx0
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx0.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx0.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx0.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx0.ne' (by norm_num)
  have hl30 := log_thirty_ge
  have hs := stir_log_thirty
  linarith

end PI.PC
end
end

