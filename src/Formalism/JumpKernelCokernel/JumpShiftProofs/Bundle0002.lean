module

public import Formalism.JumpKernelCokernel.Statement

@[expose] public section

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom
section
namespace Formalism.KernelCokernelLengths

theorem power_binomial_bound : PowBinom := by
  intro A _ ℓ u ε q b Y hℓ hY
  set k := (Y - 1) / ℓ with hk
  set I : Ideal A := Ideal.span {(ℓ : A), q ^ ℓ} with hI
  have hYle : Y ≤ ℓ * (k + 1) := by
    have h := Nat.lt_mul_div_succ (Y - 1) (show 0 < ℓ by omega)
    rw [← hk] at h
    omega
  have hmem : (u * q ^ ℓ + (ℓ : A) * ε) ^ b ∈
      Ideal.span {(ℓ : A) ^ (b - k)} ⊔ Ideal.span {q ^ Y} * I ^ (b - k - 1) := by
    rw [add_pow]
    refine Ideal.sum_mem _ (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    by_cases hmk : m ≤ k
    · apply Ideal.mem_sup_left
      rw [Ideal.mem_span_singleton]
      have h1 : (ℓ : A) ^ (b - k) ∣ ((ℓ : A) * ε) ^ (b - m) := by
        rw [mul_pow]; exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _
    · apply Ideal.mem_sup_right
      obtain ⟨e, rfl⟩ : ∃ e, m = k + 1 + e := ⟨m - (k + 1), by omega⟩
      have hℓI : (ℓ : A) ∈ I := Ideal.subset_span (by simp)
      have hqI : q ^ ℓ ∈ I := Ideal.subset_span (by simp)
      have hin : (q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) ∈ I ^ (b - k - 1) := by
        have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hqI e)
          (Ideal.pow_mem_pow hℓI (b - (k + 1 + e)))
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
      have hp : q ^ (ℓ * (k + 1)) = q ^ Y * q ^ (ℓ * (k + 1) - Y) := by
        rw [← pow_add]; congr 1; omega
      have heq : (u * q ^ ℓ) ^ (k + 1 + e) * ((ℓ : A) * ε) ^ (b - (k + 1 + e)) *
            (b.choose (k + 1 + e) : A) =
          q ^ Y * ((q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) *
            (u ^ (k + 1 + e) * q ^ (ℓ * (k + 1) - Y) * ε ^ (b - (k + 1 + e)) *
              (b.choose (k + 1 + e) : A))) := by
        have hq : (q ^ ℓ) ^ (k + 1 + e) = q ^ Y * q ^ (ℓ * (k + 1) - Y) * (q ^ ℓ) ^ e := by
          rw [pow_add, ← pow_mul, hp]
        rw [mul_pow, mul_pow, hq]
        ring
      rw [heq]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hin)
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hc
  exact ⟨α, β, by rw [← hac]; ring, hβ⟩

end Formalism.KernelCokernelLengths
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.RowDegreeBound
section
namespace Formalism.KernelCokernelLengths

theorem row_degree_bound : RowD := by
  unfold RowD
  intro h h1 η hη
  have key : 32 * (h1 + η) ≤ 50 * h1 := by omega
  gcongr ?_ / _
  exact_mod_cast key

end Formalism.KernelCokernelLengths
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA
section
namespace Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Filter

lemma coef_le (x : ℝ) (hx : 11 ≤ x) : (2 * x - 1) / (x - 1) ^ 2 ≤ 21 / 100 := by
  rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < (x - 1) ^ 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ x - 11 / 21)]

lemma coef_nonneg (x : ℝ) (hx : 11 ≤ x) : 0 ≤ (2 * x - 1) / (x - 1) ^ 2 := by
  exact div_nonneg (by linarith) (sq_nonneg _)

lemma one_le_log (x : ℝ) (hx : 11 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

lemma logb_le (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : Real.logb x y ≤ Real.log y := by
  rw [Real.logb]
  exact div_le_self (Real.log_nonneg hy) (one_le_log x hx)

lemma logb_nonneg' (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : 0 ≤ Real.logb x y := by
  rw [Real.logb]
  exact div_nonneg (Real.log_nonneg hy) (by linarith [one_le_log x hx])

lemma eventually_log (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 13 + 2 * Real.log (4 * (n : ℝ)) ≤ c * n := by
  refine ⟨⌈256 / c ^ 2 + 26 / c⌉₊ + 1, fun n hn => ?_⟩
  have hA : 0 ≤ 256 / c ^ 2 := by positivity
  have hB : 0 ≤ 26 / c := by positivity
  have hnR : 256 / c ^ 2 + 26 / c + 1 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (256 / c ^ 2 + 26 / c)
    have h2 : ((⌈256 / c ^ 2 + 26 / c⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log (4 * n) ≤ 2 * Real.sqrt (4 * n) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 4 * n))
    rw [Real.log_sqrt (by positivity)] at h
    linarith [Real.sqrt_nonneg (4 * (n : ℝ))]
  have hsq : Real.sqrt (4 * n) = 2 * Real.sqrt n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hs16 : 16 / c ≤ Real.sqrt n := by
    have h1 : (16 / c) ^ 2 ≤ (n : ℝ) := by
      have : (16 / c) ^ 2 = 256 / c ^ 2 := by ring
      linarith
    calc 16 / c = Real.sqrt ((16 / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1
  have h16 : 16 ≤ c * Real.sqrt n := by
    rw [div_le_iff₀ hc] at hs16
    linarith
  have h26 : 26 ≤ c * n := by
    have : 26 / c ≤ (n : ℝ) := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  have hcn : c * n = (c * Real.sqrt n) * Real.sqrt n := by rw [mul_assoc, hss]
  nlinarith [mul_le_mul_of_nonneg_right h16 hs0]

end Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas in
theorem Formalism.KernelCokernelLengths.thickness_first_bound : Formalism.KernelCokernelLengths.ThickA := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_log (ε / 2) (by linarith)
  refine ⟨min (1 / 10) (ε / 10), by positivity, max N 4, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hδ1 : min (1 / 10) (ε / 10) ≤ 1 / 10 := min_le_left _ _
  have hδε : min (1 / 10) (ε / 10) ≤ ε / 10 := min_le_right _ _
  have hbN : N ≤ b := le_trans (le_max_left _ _) hb
  have hb4 : 4 ≤ b := le_trans (le_max_right _ _) hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hb4R : (4 : ℝ) ≤ b := by exact_mod_cast hb4
  have hℓ' : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hH1 : (1 : ℝ) ≤ 2 * ((h + (η + t + 1) : ℕ) : ℝ) := by
    have : 1 ≤ h + (η + t + 1) := by omega
    have : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hHle : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by
    have : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
    exact_mod_cast this
  have hδb : min (1 / 10) (ε / 10) * (b : ℝ) ≤ ε / 10 * b := mul_le_mul_of_nonneg_right hδε hb0
  have hδb1 : min (1 / 10) (ε / 10) * (b : ℝ) ≤ 1 / 10 * b := mul_le_mul_of_nonneg_right hδ1 hb0
  have hcoef := coef_le ℓ hℓ'
  have hcoef0 := coef_nonneg ℓ hℓ'
  have hlogb := logb_le ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have hlogb0 := logb_nonneg' ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have h2H : 2 * ((h + (η + t + 1) : ℕ) : ℝ) ≤ 4 * b := by
    have hη' : (η : ℝ) ≤ 1 / 10 * b := le_trans hη hδb1
    have hS' : (S : ℝ) ≤ 1 / 10 * b := le_trans hS hδb1
    have ht' : (t : ℝ) ≤ 1 / 10 * b := le_trans ht hδb1
    linarith
  have hlog2H : Real.log (2 * ((h + (η + t + 1) : ℕ) : ℝ)) ≤ Real.log (4 * b) :=
    Real.log_le_log (by linarith) h2H
  have hlogN := hN b hbN
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) =
      ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) + 3 +
        (Real.logb (ℓ : ℝ) (2 * ((h + (η + t + 1) : ℕ) : ℝ)) + 1) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    rw [mul_div_assoc]
  have hHc : ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) ≤
      ((h + (η + t + 1) : ℕ) : ℝ) * (21 / 100) :=
    mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) := by
    rw [haR]
    have := mul_nonneg (Nat.cast_nonneg (h + (η + t + 1))) hcoef0
    linarith
  have hceil : (⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ : ℝ) ≤
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) + 1 := (Nat.ceil_lt_add_one haR0).le
  have hεb : 0 ≤ ε * (b : ℝ) := mul_nonneg hε.le hb0
  push_cast
  push_cast at hHle hHc hceil haR hlogb hlog2H
  linarith
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB
section
namespace Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

lemma coef_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) :
    (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ 21 / 100 := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpos : 0 < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 21 * ℓ - 11)]

lemma log_two_le (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 100 + 98 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 100 by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)
  have h3 : Real.log x = Real.log (x / 100) + Real.log 100 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    field_simp
  linarith

lemma one_le_log (ℓ : ℕ) (hℓ : 11 ≤ ℓ) : 1 ≤ Real.log (ℓ : ℝ) := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma logb_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    Real.logb (ℓ : ℝ) x ≤ Real.log x := by
  exact div_le_self (Real.log_nonneg hx) (one_le_log ℓ hℓ)

lemma logb_nonneg' (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ Real.logb (ℓ : ℝ) x := by
  have h : (1 : ℝ) < ℓ := by
    have : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  exact Real.logb_nonneg h hx

end Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas in
theorem Formalism.KernelCokernelLengths.thickness_second_bound : Formalism.KernelCokernelLengths.ThickB := by
  refine ⟨1 / 100, by norm_num, 10000, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hbR : (10000 : ℝ) ≤ b := by exact_mod_cast hb
  have hη' : 100 * η ≤ b := by
    have : ((100 * η : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have hS' : 100 * S ≤ b := by
    have : ((100 * S : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have ht' : 100 * t ≤ b := by
    have : ((100 * t : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  refine ⟨by omega, by omega, ?_⟩
  have hHn : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
  have hH1 : 1 ≤ h + (η + t + 1) := by omega
  have hHR : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by exact_mod_cast hHn
  have hH1R : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast hH1
  have hbi : b ≤ bi + t + 1 := h1
  have hbiR : (b : ℝ) ≤ bi + t + 1 := by exact_mod_cast hbi
  set H : ℕ := h + (η + t + 1) with hHdef
  have hx1 : (1 : ℝ) ≤ 2 * (H : ℝ) := by linarith
  have hlb := logb_le ℓ hℓ (2 * (H : ℝ)) hx1
  have hlb0 := logb_nonneg' ℓ hℓ (2 * (H : ℝ)) hx1
  have hlog := log_two_le (2 * (H : ℝ)) (by linarith)
  have hc := coef_le ℓ hℓ
  have hcoef0 : 0 ≤ (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    apply div_nonneg <;> nlinarith
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hA : (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hc hH0
  have hA0 : 0 ≤ (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc]; positivity
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H ≤ (H : ℝ) * (21 / 100) + 4 + ((2 * (H : ℝ)) / 100 + 98) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have hceil := Nat.ceil_lt_add_one haR0
  have hηR : (100 : ℝ) * η ≤ b := by exact_mod_cast hη'
  have hSR : (100 : ℝ) * S ≤ b := by exact_mod_cast hS'
  have htR : (100 : ℝ) * t ≤ b := by exact_mod_cast ht'
  have key : ((2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H⌉₊ + (η + t + 1) + 1 : ℕ) : ℝ) ≤ (bi : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast key
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer
section
noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open PowerSeries

theorem len_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (v : ℕ) :
    Module.length O (O ⧸ Ideal.span {(u : O) * ϖ ^ v}) = v := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) v

theorem ker_eq_coker {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) :
    Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f) := by
  have h1 : Module.length O M =
      Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
      (Submodule.subtype_injective _) f.surjective_rangeRestrict
      (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length O M =
      Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hR : Module.length O (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective _ (Submodule.subtype_injective (LinearMap.range f)))
  have h5 : Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) =
      Module.length O (M ⧸ LinearMap.range f) + Module.length O (LinearMap.range f) := by
    rw [← h1, h2, add_comm]
  exact WithTop.add_right_cancel hR h5

variable {O : Type} [CommRing O] (ℓ : O) (n k : ℕ)

abbrev J : Ideal (PowerSeries O) := Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

noncomputable abbrev ψ : Polynomial O →+* (PowerSeries O ⧸ J ℓ n k) :=
  Polynomial.eval₂RingHom (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X)

theorem psi_apply (P : Polynomial O) :
    ψ ℓ n k P = P.eval₂ (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X) := rfl

theorem alg_eq (a : O) :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) a = Ideal.Quotient.mk (J ℓ n k) (C a) := rfl

theorem psi_eq (P : Polynomial O) : ψ ℓ n k P = Ideal.Quotient.mk (J ℓ n k) (P : PowerSeries O) := by
  have h : ψ ℓ n k = (Ideal.Quotient.mk (J ℓ n k)).comp (Polynomial.coeToPowerSeries.ringHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [alg_eq]
    · simp
  rw [h]
  rfl

theorem mk_eq_psi (p : PowerSeries O) :
    Ideal.Quotient.mk (J ℓ n k) p = ψ ℓ n k (trunc n p) := by
  rw [psi_eq, Ideal.Quotient.eq]
  obtain ⟨q, hq⟩ : (X : PowerSeries O) ^ n ∣ p - (trunc n p : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hm]
  rw [hq]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem algebraMap_pow_k :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) (ℓ ^ k) = 0 := by
  rw [alg_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

theorem smul_pow_k (b : PowerSeries O ⧸ J ℓ n k) : ℓ ^ k • b = 0 := by
  rw [Algebra.smul_def, algebraMap_pow_k, zero_mul]

theorem len_B_le :
    Module.length O (PowerSeries O ⧸ J ℓ n k) ≤
      Module.length O (Fin n → O ⧸ Ideal.span {ℓ ^ k}) := by
  let e : Fin n → (PowerSeries O ⧸ J ℓ n k) := fun j => (Ideal.Quotient.mk (J ℓ n k) X) ^ (j : ℕ)
  have hker : ∀ j, Ideal.span {ℓ ^ k} ≤ LinearMap.ker (LinearMap.toSpanSingleton O _ (e j)) := by
    intro j
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact smul_pow_k ℓ n k _
  let Φ : (Fin n → O ⧸ Ideal.span {ℓ ^ k}) →ₗ[O] (PowerSeries O ⧸ J ℓ n k) :=
    ∑ j : Fin n, (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j)).comp
      (LinearMap.proj j)
  have hΦ : Function.Surjective Φ := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨fun j => Ideal.Quotient.mk _ (coeff (j : ℕ) p), ?_⟩
    rw [mk_eq_psi, psi_apply, eval₂_trunc_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range]
    simp only [Φ]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j))
      (Submodule.Quotient.mk (coeff (j : ℕ) p)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  exact Module.length_le_of_surjective Φ hΦ

theorem len_coker_le :
    Module.length O ((PowerSeries O ⧸ J ℓ n k) ⧸ LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))) ≤
      Module.length O (O ⧸ Ideal.span {ℓ ^ k}) := by
  set R := LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ))) with hR
  have hker : Ideal.span {ℓ ^ k} ≤
      LinearMap.ker (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k))) := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← LinearMap.map_smul, smul_pow_k, map_zero]
  let Ψ := Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k)))
    hker
  have hΨ : Function.Surjective Ψ := by
    intro z
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective R z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := ℓ) (p := trunc n p)
    refine ⟨Submodule.Quotient.mk ((trunc n p).eval ℓ), ?_⟩
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul,
      Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-ψ ℓ n k Q, ?_⟩
    have hX : Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ) =
        ψ ℓ n k (Polynomial.X - Polynomial.C ℓ) := by
      rw [psi_eq, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
    rw [map_neg, LinearMap.mulLeft_apply, hX, ← map_mul, ← hQ, map_sub, mk_eq_psi ℓ n k p,
      psi_apply ℓ n k (Polynomial.C _), Polynomial.eval₂_C,
      Algebra.algebraMap_eq_smul_one, neg_sub]
  exact Module.length_le_of_surjective Ψ hΨ

end Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas in
theorem Formalism.KernelCokernelLengths.torsion_kernel_length : Formalism.KernelCokernelLengths.TorsKer := by
  intro O _ _ _ ℓ hℓ n k
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ hϖ
  have hl1 : Module.length O (O ⧸ Ideal.span {ℓ}) = v := by
    rw [hu]; exact len_quot_pow hϖ u v
  have hlk : Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = ((v * k : ℕ) : ℕ∞) := by
    rw [hu, mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val]
    exact len_quot_pow hϖ (u ^ k) (v * k)
  have hB : Module.length O (PowerSeries O ⧸ J ℓ n k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (len_B_le ℓ n k)
    rw [Module.length_pi, hlk, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  rw [ker_eq_coker hB, hl1]
  refine (len_coker_le ℓ n k).trans ?_
  rw [hlk]
  push_cast
  rw [mul_comm]
end
end

