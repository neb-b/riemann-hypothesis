module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronSum
section
noncomputable section

namespace PI.EF

open Finset

theorem sum_rpow_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) ≤ 1 / ε := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + ε))) (Set.Icc 1 (1 + (K : ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  beta_reduce at h1
  have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (K : ℝ)) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨fun h => by linarith, h0⟩)] at h1
  have hexp : -(1 + ε) + 1 = -ε := by ring
  rw [hexp, Real.one_rpow] at h1
  have hpos : 0 ≤ (1 + (K : ℝ)) ^ (-ε) := Real.rpow_nonneg (by linarith) _
  have hrhs : ((1 + (K : ℝ)) ^ (-ε) - 1) / (-ε) ≤ 1 / ε := by
    rw [div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  calc ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))
      = ∑ i ∈ range K, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 + ε)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        ring
    _ ≤ _ := h1
    _ ≤ 1 / ε := hrhs

def logTerm (c : ℝ) (n : ℕ) : ℝ := Real.log n * (n : ℝ) ^ (-c)

theorem logTerm_nonneg (c : ℝ) (n : ℕ) : 0 ≤ logTerm c n := by
  exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem sum_logTerm_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ n ∈ range K, logTerm (1 + 2 * ε) n ≤ 1 / ε ^ 2 := by
  have e0 : logTerm (1 + 2 * ε) 0 = 0 := by simp [logTerm]
  have e1 : logTerm (1 + 2 * ε) 1 = 0 := by simp [logTerm]
  have hb : ∀ i : ℕ, logTerm (1 + 2 * ε) (i + 2) ≤ ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
    intro i
    unfold logTerm
    push_cast
    have hx : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hl := Real.log_le_rpow_div hx.le hε
    have hp : 0 ≤ ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := Real.rpow_nonneg hx.le _
    calc Real.log ((i : ℝ) + 2) * ((i : ℝ) + 2) ^ (-(1 + 2 * ε))
        ≤ ((i : ℝ) + 2) ^ ε / ε * ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := mul_le_mul_of_nonneg_right hl hp
      _ = ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hx]
        congr 2
        ring
  calc ∑ n ∈ range K, logTerm (1 + 2 * ε) n
      ≤ ∑ n ∈ range (K + 2), logTerm (1 + 2 * ε) n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => logTerm_nonneg _ n)
    _ = ∑ i ∈ range K, logTerm (1 + 2 * ε) (i + 2) := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [zero_add, e0, e1, add_zero]
    _ ≤ ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := Finset.sum_le_sum fun i _ => hb i
    _ = (∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))) / ε := (Finset.sum_div _ _ _).symm
    _ ≤ (1 / ε) / ε := div_le_div_of_nonneg_right (sum_rpow_le hε K) hε.le
    _ = 1 / ε ^ 2 := by ring

theorem kb_nonneg {T : ℝ} (hT : 0 < T) (y : ℝ) : 0 ≤ kb T y := by
  unfold kb
  split_ifs
  · norm_num
  · exact div_nonneg zero_le_one (mul_nonneg hT.le (abs_nonneg _))

theorem kb_le_two {T : ℝ} (_hT : 0 < T) (y : ℝ) : kb T y ≤ 2 := by
  unfold kb
  split_ifs with h
  · exact le_rfl
  · have h' := not_le.mp h
    rw [div_le_iff₀ (by linarith)]
    linarith

theorem kb_le_of_le {T d y : ℝ} (hT : 0 < T) (hd : 0 < d) (h : d ≤ |Real.log y|) :
    kb T y ≤ 2 / (T * d) := by
  have hTd : 0 < T * d := mul_pos hT hd
  have hle : T * d ≤ T * |Real.log y| := mul_le_mul_of_nonneg_left h hT.le
  unfold kb
  split_ifs with h1
  · rw [le_div_iff₀ hTd]
    linarith
  · calc 1 / (T * |Real.log y|) ≤ 1 / (T * d) := one_div_le_one_div_of_le hTd hle
      _ ≤ 2 / (T * d) := div_le_div_of_nonneg_right (by norm_num) hTd.le

theorem abs_log_div_ge_far {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (h : x ≤ u / 2 ∨ 2 * u ≤ x) :
    Real.log 2 ≤ |Real.log (u / x)| := by
  rcases h with h | h
  · have h2 : 2 ≤ u / x := by
      rw [le_div_iff₀ hx]
      linarith
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)
  · have h2 : 2 ≤ x / u := by
      rw [le_div_iff₀ hu]
      linarith
    have hflip : Real.log (u / x) = -Real.log (x / u) := by
      rw [← Real.log_inv, inv_div]
    rw [hflip, abs_neg]
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)

theorem log_ge_half {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h2 := Real.log_le_log (by norm_num) hu
  have h3 := Real.log_two_gt_d9
  linarith

theorem cLine_le_three {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  have hl := log_ge_half hu
  have h : 1 / Real.log u ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  unfold cLine
  linarith

theorem cLine_pos {u : ℝ} (hu : 2 ≤ u) : 0 < cLine u := by
  have hl := log_ge_half hu
  have h : 0 < 1 / Real.log u := one_div_pos.mpr (by linarith)
  unfold cLine
  linarith

theorem rpow_cLine {u : ℝ} (hu : 2 ≤ u) : u ^ cLine u = Real.exp 1 * u := by
  have hu0 : 0 < u := by linarith
  have hl : Real.log u ≠ 0 := by linarith [log_ge_half hu]
  unfold cLine
  rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, mul_one_div_cancel hl, mul_comm]

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronTruncOf
section
namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

lemma one_lt_cLine {u : ℝ} (hu : 2 ≤ u) : 1 < cLine u := by
  have h := Real.log_pos (by linarith : (1:ℝ) < u)
  have h2 := one_div_pos.mpr h
  show 1 < 1 + 1 / Real.log u
  linarith

lemma kernel_le_kb (hK : PerronKernel) (y c T : ℝ) (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c * kb T y := by
  obtain ⟨h1, h2⟩ := hK y c T hy hc hT
  by_cases h : T * |Real.log y| ≤ 1
  · rw [kb, if_pos h]
    linarith
  · rw [kb, if_neg h]
    push_neg at h
    rw [mul_one_div, le_div_iff₀ (by linarith)]
    linarith

lemma term_mul_kernel (a : ℕ → ℂ) (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    term a s n * ((u : ℂ) ^ s / s) = a n * (((u / n : ℝ) : ℂ) ^ s / s) := by
  rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hu.le (Nat.cast_nonneg n)]
  push_cast
  ring

theorem perronTrunc_of {C : ℝ} (hK : PerronKernel) (hS : PerronSumBound C) : PerronTrunc C := by
  intro a ha u T hu hT
  have hc1 : 1 < cLine u := one_lt_cLine hu
  set c := cLine u with hcdef
  have hc0 : 0 < c := by linarith
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hSs, hSle⟩ := hS u T hu hT
  have ha0 : a 0 = 0 := by
    have h := ha 0
    rw [ArithmeticFunction.map_zero] at h
    exact norm_le_zero_iff.mp h

  have hΛsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)
    refine Complex.summable_ofReal.mp (h.congr (fun n => ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl
  have hterm : ∀ (n : ℕ) (s : ℂ), s.re = c →
      ‖LSeries.term a s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c := by
    intro n s hs
    rw [LSeries.norm_term_eq, hs]
    split_ifs with hn
    · subst hn
      simp
    · exact div_le_div_of_nonneg_right (ha n) (by positivity)
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  have hkern : ∀ t : ℝ, ‖(u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ u ^ c / c := by
    intro t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]
    apply div_le_div_of_nonneg_left (by positivity) hc0
    have h := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    rw [hre, abs_of_pos hc0] at h
    exact h

  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := -T) (b := T)
    (F := fun (n : ℕ) (t : ℝ) => LSeries.term a ((c : ℂ) + t * I) n *
      ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (f := fun t : ℝ => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (fun n _ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c * (u ^ c / c))
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, zero_mul]
        exact MeasureTheory.aestronglyMeasurable_const
      · simp only [LSeries.term_of_ne_zero hn]
        apply Measurable.aestronglyMeasurable
        fun_prop)
    (fun n => Filter.Eventually.of_forall (fun t _ => by
      rw [norm_mul]
      exact mul_le_mul (hterm n _ (hre t)) (hkern t) (norm_nonneg _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))))
    (Filter.Eventually.of_forall (fun t _ => hΛsum.mul_right _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => by
      have hsum : LSeriesSummable a ((c : ℂ) + t * I) :=
        Summable.of_norm_bounded hΛsum (fun n => hterm n _ (hre t))
      exact hsum.hasSum.mul_right _))

  have hG : HasSum (fun n : ℕ => a n * perronK (u / n) c T)
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, LSeries a ((c : ℂ) + t * I) *
        ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) := by
    have hfun : (fun n : ℕ => a n * perronK (u / n) c T) = fun n : ℕ => (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
          ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [ha0, LSeries.term_zero]
      · have h1 : (∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
              ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) =
            a n * ∫ t : ℝ in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext t
          exact term_mul_kernel a u hu0 n hn _
        rw [h1, perronK]
        ring
    rw [hfun]
    exact hDC.mul_left _

  have hind : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) := by
    have h : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [ha0]
      · push_neg at hn
        have hlt : u < n := by
          have h1 := Nat.lt_floor_add_one u
          have h2 : (⌊u⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
          linarith
        have h3 : ¬ (1 ≤ u / n) := by
          rw [not_le, div_lt_one (by linarith)]
          exact hlt
        simp [h3]
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnu : (n : ℝ) ≤ u := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hu0.le)
    have h4 : 1 ≤ u / n := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    simp [h4]
  have hdiff := hind.sub hG
  rw [← hdiff.tsum_eq]
  calc _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (u / n) ^ c * kb T (u / n) := by
        apply tsum_of_norm_bounded hSs.hasSum
        intro n
        rw [← mul_sub, norm_mul]
        rcases eq_or_ne n 0 with rfl | hn
        · simp [ha0]
        · have hy : 0 < u / n := div_pos hu0 (by exact_mod_cast Nat.pos_of_ne_zero hn)
          have h1 := kernel_le_kb hK (u / n) c T hy hc0 hT0
          rw [norm_sub_rev] at h1
          rw [mul_assoc]
          exact mul_le_mul (ha n) h1 (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := hSle

end PI.EF.PK
end

