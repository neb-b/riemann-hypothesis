module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0028
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0029

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyper
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

namespace Hyp

theorem g_mono (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (Real.log b + 1) / √b ≤ 2 * ((Real.log a + 1) / √a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hL : 0 ≤ Real.log a := Real.log_nonneg ha
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hsb : 0 < √b := Real.sqrt_pos.2 hb0
  set s := √b / √a with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hsa, one_mul]
    exact Real.sqrt_le_sqrt hab
  have hs0 : 0 < s := by linarith
  have hsb' : √b = √a * s := by
    rw [hs]
    field_simp
  have hb' : b = a * s ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt ha0.le]
    field_simp
  have hlogb : Real.log b = Real.log a + 2 * Real.log s := by
    rw [hb', Real.log_mul ha0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hsb', hlogb, div_le_iff₀ (by positivity)]
  have e : 2 * ((Real.log a + 1) / √a) * (√a * s) = 2 * (Real.log a + 1) * s := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hs1 hL]

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem diff_bound (hχ : χ ≠ 1) (N₀ N₁ : ℕ) (h0 : 1 ≤ N₀) (h01 : N₀ ≤ N₁) :
    (cF χ N₁ - cF χ N₀).re ≤ ‖DirichletCharacter.LFunction χ 1‖ * (Real.log N₁ - Real.log N₀) +
      86 * ((q : ℝ) + 1) * ((Real.log N₀ + 1) / √(N₀ : ℝ)) := by
  set L := DirichletCharacter.LFunction χ 1
  set U₀ := Nat.sqrt N₀ with hU₀
  set U₁ := Nat.sqrt N₁ with hU₁
  set B := (q : ℝ) + 1 with hBdef
  have hB : 1 ≤ B := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hU01 : U₀ ≤ U₁ := Nat.sqrt_le_sqrt h01
  have hU0 : 1 ≤ U₀ := Nat.sqrt_pos.mpr (by omega)
  have hR1 := cF_approx χ hχ N₁ (by omega)
  have hR0 := cF_approx χ hχ N₀ h0
  have hT := cT_diff χ hχ U₀ U₁ hU0 hU01
  set R₁ := cF χ N₁ - (((Real.log N₁ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₁)
  set R₀ := cF χ N₀ - (((Real.log N₀ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₀)
  set t := Real.log N₁ - Real.log N₀ with ht
  have ht0 : 0 ≤ t := by
    have := Real.log_le_log (by linarith) hN01r; linarith
  set W := -(cT χ U₁ - cT χ U₀) + R₁ - R₀ with hW
  have eD : cF χ N₁ - cF χ N₀ = (t : ℂ) * L + W := by
    simp only [hW, R₁, R₀, ht]; push_cast; ring
  rw [eD, Complex.add_re, Complex.re_ofReal_mul]
  have hLre : L.re ≤ ‖L‖ := Complex.re_le_norm L
  have hWre : W.re ≤ ‖W‖ := Complex.re_le_norm W
  have hWn : ‖W‖ ≤ ‖cT χ U₁ - cT χ U₀‖ + ‖R₁‖ + ‖R₀‖ := by
    rw [hW]
    calc ‖-(cT χ U₁ - cT χ U₀) + R₁ - R₀‖ ≤ ‖-(cT χ U₁ - cT χ U₀) + R₁‖ + ‖R₀‖ := norm_sub_le _ _
      _ ≤ ‖-(cT χ U₁ - cT χ U₀)‖ + ‖R₁‖ + ‖R₀‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hg := g_mono (N₀ : ℝ) (N₁ : ℝ) hN0r hN01r
  set g₀ := (Real.log N₀ + 1) / √(N₀ : ℝ)
  have hg0 : 0 ≤ g₀ := div_nonneg (by linarith [Real.log_natCast_nonneg N₀]) (Real.sqrt_nonneg _)
  have hR1' : ‖R₁‖ ≤ 52 * B * g₀ := by
    have e : 26 * B * (Real.log N₁ + 1) / √(N₁ : ℝ) = 26 * B * ((Real.log N₁ + 1) / √(N₁ : ℝ)) := by ring
    rw [e] at hR1
    have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 26 * B)
    nlinarith
  have hR0' : ‖R₀‖ ≤ 26 * B * g₀ := by
    have e : 26 * B * (Real.log N₀ + 1) / √(N₀ : ℝ) = 26 * B * g₀ := by ring
    rw [e] at hR0; exact hR0
  have hT' : ‖cT χ U₁ - cT χ U₀‖ ≤ 8 * B * g₀ := by
    have hUr : (1 : ℝ) ≤ U₀ := by exact_mod_cast hU0
    have hUN : U₀ ≤ N₀ := Nat.sqrt_le_self N₀
    have hUNr : (U₀ : ℝ) ≤ N₀ := by exact_mod_cast hUN
    have hlt : N₀ < (U₀ + 1) * (U₀ + 1) := Nat.lt_succ_sqrt N₀
    have hltr : (N₀ : ℝ) < ((U₀ : ℝ) + 1) * ((U₀ : ℝ) + 1) := by exact_mod_cast hlt
    have hsU : √(N₀ : ℝ) < (U₀ : ℝ) + 1 := by
      have := Real.sqrt_lt_sqrt (Nat.cast_nonneg N₀) hltr
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog : Real.log ((U₀ : ℝ) + 1) ≤ 1 + Real.log N₀ := by
      have h1 : Real.log ((U₀ : ℝ) + 1) ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have := Real.log_two_lt_d9
      linarith
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    have h2 : (1 + Real.log ((U₀ : ℝ) + 1)) / ((U₀ : ℝ) + 1) ≤ 2 * g₀ := by
      have e : 2 * g₀ = 2 * (Real.log N₀ + 1) / √(N₀ : ℝ) := by ring
      rw [e, div_le_div_iff₀ (by linarith) hs0]
      nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * B)
    linarith
  have hLt : t * L.re ≤ ‖L‖ * t := by nlinarith
  linarith

end Hyp

theorem deuring_heilbronn_hypergeometric : DHHyper := by
  refine ⟨400, by norm_num, ?_⟩
  intro M _ χ₁ y x hM _ hne hy hyx
  have e : ∀ N₀ N₁ : ℕ, N₀ ≤ N₁ → ∑ n ∈ Finset.Ioc N₀ N₁, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) =
      (Hyp.cF χ₁ N₁ - Hyp.cF χ₁ N₀).re := by
    intro N₀ N₁ h
    rw [Hyp.cF, Hyp.cF, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N₀) h, add_sub_cancel_left,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.div_natCast_re]
  have h0 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have h01 : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
  rw [e _ _ h01]
  have hd := Hyp.diff_bound χ₁ hne ⌊y⌋₊ ⌊x⌋₊ h0 h01
  set N₀ := ⌊y⌋₊ with hN₀
  set N₁ := ⌊x⌋₊ with hN₁
  set L := DirichletCharacter.LFunction χ₁ 1
  set B := (M : ℝ) + 1 with hBdef
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hN0y : (N₀ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyN0 : y < N₀ + 1 := Nat.lt_floor_add_one y
  have hN1x : (N₁ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy

  have hlog1 : Real.log N₁ ≤ Real.log x := Real.log_le_log (by linarith) hN1x
  have hlog0 : Real.log y - Real.log N₀ ≤ 2 / y := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.log_le_sub_one_of_pos (show 0 < y / N₀ by positivity)
    have h' : y / N₀ - 1 ≤ 2 / y := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith
  have hxy : Real.log (x / y) = Real.log x - Real.log y := Real.log_div (by linarith) (by linarith)

  have hLB : ‖L‖ ≤ 5 * B := by
    have h := Hyp.cS_approx χ₁ hne 1 le_rfl
    have h1 : Hyp.cS χ₁ 1 = 1 := by simp [Hyp.cS]
    rw [h1] at h
    have := norm_sub_norm_le L 1
    simp only [norm_one, Nat.cast_one, div_one] at h this
    linarith

  have hsy : 0 < √y := Real.sqrt_pos.mpr (by linarith)
  have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsyN : √y ≤ 2 * √(N₀ : ℝ) := by
    have h4 : (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) = 4 * N₀ := by
      have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) N₀); nlinarith
    have := Real.sqrt_le_sqrt (show y ≤ (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) by rw [h4]; linarith)
    rwa [Real.sqrt_mul_self (by positivity)] at this
  have hlN0 : Real.log N₀ ≤ Real.log y := Real.log_le_log (by linarith) hN0y
  set Y := (Real.log y + 1) / √y with hY
  have hY0 : 0 ≤ Y := by positivity
  have hg0 : (Real.log N₀ + 1) / √(N₀ : ℝ) ≤ 2 * Y := by
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ hs0 hsy]
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    nlinarith
  have hyY : 2 / y ≤ 2 * Y := by
    have hsyy : √y ≤ y := by
      have := Real.sqrt_le_sqrt (show y ≤ y * y by nlinarith)
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ (by linarith) hsy]
    nlinarith
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have i1 : ‖L‖ * (Real.log N₁ - Real.log N₀) ≤ ‖L‖ * Real.log (x / y) + ‖L‖ * (2 / y) := by
    rw [hxy, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hLn
  have i2 : ‖L‖ * (2 / y) ≤ 5 * B * (2 * Y) := mul_le_mul hLB hyY (by positivity) (by positivity)
  have i3 : 86 * B * ((Real.log N₀ + 1) / √(N₀ : ℝ)) ≤ 86 * B * (2 * Y) :=
    mul_le_mul_of_nonneg_left hg0 (by positivity)
  have e3 : 400 * (M : ℝ) * (Real.log y + 1) / √y = 400 * M * Y := by rw [hY]; ring
  rw [e3]
  have hB2 : B ≤ 2 * M := by rw [hBdef]; linarith
  have i4 : 5 * B * (2 * Y) + 86 * B * (2 * Y) ≤ 400 * M * Y := by nlinarith
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrime
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

lemma dhpr_partial {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ CT CH A : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hCT : 0 ≤ CT) (hCH : 0 ≤ CH) (hA0 : 0 ≤ A)
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y)
    (hHyp : ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        A * Real.log (x / y) + CH * M * (Real.log y + 1) / Real.sqrt y)
    (v0 : ℕ) (hv0pos : 0 < v0) (N : ℕ) :
    ∑ n ∈ range N, dhprF χ₁ k σ n ≤ 2 * CT * (v0 : ℝ) ^ (k + 1) +
      (2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / (σ - 1) ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / (σ - 1) ^ (k + 1) *
          (20 * Real.exp (-((v0 : ℝ) / 4))))) := by
  have hη : 0 < σ - 1 := by linarith
  have hvV : v0 ≤ v0 + N := Nat.le_add_right _ _
  have hNZ : N ≤ ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ := by
    apply Nat.le_floor
    have := Real.add_one_le_exp ((v0 + N : ℕ) : ℝ)
    push_cast at this ⊢
    have : (0 : ℝ) ≤ v0 := Nat.cast_nonneg _
    linarith
  have hYZ := dhpr_floor_mono hvV
  have hrange : range (⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ + 1) =
      insert 0 (Ioc 0 ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊) := by
    ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega
  have hf0 : dhprF χ₁ k σ 0 = 0 := by simp [dhprF]
  have hHyp' : ∀ v : ℕ, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
      (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        A + CH * M * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
    intro v
    have h := hHyp (Real.exp (v : ℝ)) (Real.exp ((v + 1 : ℕ) : ℝ))
      (Real.one_le_exp (Nat.cast_nonneg v)) (Real.exp_le_exp.mpr (by push_cast; linarith))
    rwa [dhpr_hyper_simp] at h
  calc ∑ n ∈ range N, dhprF χ₁ k σ n
      ≤ ∑ n ∈ range (⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ + 1), dhprF χ₁ k σ n :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
          (fun n _ _ => dhpr_term_nonneg χ₁ h1 k n σ)
    _ = ∑ n ∈ Ioc 0 ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n := by
        rw [hrange, sum_insert (by simp), hf0, zero_add]
    _ = ∑ n ∈ Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n +
          ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n :=
        (sum_Ioc_consecutive _ (Nat.zero_le _) hYZ).symm
    _ ≤ _ := add_le_add (dhpr_small χ₁ h1 k hσ.le v0 hv0pos hCT hMert)
        (dhpr_large χ₁ h1 k hσ.le rfl hη (by linarith) v0 (v0 + N) hvV hA0 hCH hHyp')

lemma dhpr_arith (k : ℕ) {CT CD CH C A ℓ lam η F E M v0 : ℝ}
    (hCT : 0 ≤ CT) (hCD : 0 ≤ CD) (hCH : 0 ≤ CH)
    (hC1 : 30 * CD ≤ C) (hC2 : 18 * CT + 9 ≤ C) (hC3 : 110 * CH ≤ C)
    (hM0 : 0 < M) (hℓ1 : 1 ≤ ℓ) (hv00 : 0 ≤ v0) (hv0ℓ : v0 ≤ 9 * ℓ) (hA0 : 0 ≤ A)
    (hA : A ≤ CD * ℓ ^ 2 * lam) (hlam : 0 < lam) (hη : 0 < η) (hF : 0 < F) (hE0 : 0 ≤ E)
    (hexp : E ≤ 1 / M ^ 2) :
    2 * CT * v0 ^ (k + 1) +
      (2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E))) ≤
    (C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) + (C * ℓ) ^ (k + 1) / F
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1))) * F := by
  have hd9 := Real.exp_one_lt_d9
  have he1 : Real.exp 1 ≤ 2.72 := by norm_num at hd9 ⊢; linarith
  have he2 : Real.exp 2 ≤ 7.4 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h]; nlinarith [Real.exp_pos 1]
  have hC9 : 9 ≤ C := by linarith
  have hk : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
  have hi : 2 * CT * v0 ^ (k + 1) ≤ (C * ℓ) ^ (k + 1) := by
    calc 2 * CT * v0 ^ (k + 1) ≤ 2 * CT * (9 * ℓ) ^ (k + 1) := by gcongr
      _ = (18 * CT) * 9 ^ k * ℓ ^ (k + 1) := by ring
      _ ≤ C * C ^ k * ℓ ^ (k + 1) := by gcongr; linarith
      _ = (C * ℓ) ^ (k + 1) := by ring
  have hii : 2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2)) ≤
      C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) * F := by
    calc 2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2))
        = (4 * A * Real.exp 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1)) * (F / η ^ (k + 2)) := by ring
      _ ≤ (4 * (CD * ℓ ^ 2 * lam) * 7.4 * ((k : ℝ) + 2) * ((k : ℝ) + 2)) * (F / η ^ (k + 2)) := by
          gcongr
      _ = (29.6 * CD) * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 * (F / η ^ (k + 2)) := by ring
      _ ≤ C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 * (F / η ^ (k + 2)) := by gcongr; linarith
      _ = _ := by ring
  have hiii : 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E)) ≤
      C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1)) * F := by
    have hME : M * E ≤ 1 / M := by
      calc M * E ≤ M * (1 / M ^ 2) := by gcongr
        _ = 1 / M := by field_simp
    have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
    have hC' : 108.8 * CH ≤ C * ℓ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hℓ2 (by linarith : (0 : ℝ) ≤ C)]
    calc 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E))
        = (40 * CH * Real.exp 1 * ((k : ℝ) + 1)) * (M * E) * (F / η ^ (k + 1)) := by ring
      _ ≤ (40 * CH * 2.72 * ((k : ℝ) + 2)) * (1 / M) * (F / η ^ (k + 1)) := by gcongr
      _ = (108.8 * CH) * ((k : ℝ) + 2) * (F / (M * η ^ (k + 1))) := by field_simp; ring
      _ ≤ (C * ℓ ^ 2) * ((k : ℝ) + 2) * (F / (M * η ^ (k + 1))) := by gcongr
      _ = _ := by ring
  have hexpand : (C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) + (C * ℓ) ^ (k + 1) / F
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1))) * F =
      C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) * F + (C * ℓ) ^ (k + 1)
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1)) * F := by
    rw [add_mul, add_mul, div_mul_cancel₀ _ hF.ne']
  rw [hexpand]
  linarith

lemma dhpr_main {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (k : ℕ) {β₁ σ CH CD CT C : ℝ}
    (hM : 3 ≤ M) (h1 : χ₁ ^ 2 = 1) (hβ1 : β₁ < 1) (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (hCH : 0 ≤ CH) (hCD : 0 ≤ CD) (hCT : 0 ≤ CT)
    (hC1 : 30 * CD ≤ C) (hC2 : 18 * CT + 9 ≤ C) (hC3 : 110 * CH ≤ C)
    (hA : ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ CD * Real.log (3 * M) ^ 2 * (1 - β₁))
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y)
    (hHyp : ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y)
          + CH * M * (Real.log y + 1) / Real.sqrt y) :
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1)) := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogM3 : Real.log M ≤ Real.log (3 * M) := Real.log_le_log hM0 (by linarith)
  have hd9 := Real.exp_one_lt_d9
  have hℓ1 : 1 ≤ Real.log (3 * M) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    norm_num at hd9
    linarith
  have hF : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hA0 : 0 ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ := norm_nonneg _
  have hS : HasSum (dhprF χ₁ k σ) _ := dhpr_hasSum χ₁ k hσ
  have hv0a : 8 * Real.log M ≤ (⌈8 * Real.log M⌉₊ : ℝ) := Nat.le_ceil _
  have hv0b : (⌈8 * Real.log M⌉₊ : ℝ) < 8 * Real.log M + 1 := Nat.ceil_lt_add_one (by positivity)
  have hv0pos : 0 < ⌈8 * Real.log M⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hexp : Real.exp (-((⌈8 * Real.log M⌉₊ : ℝ) / 4)) ≤ 1 / (M : ℝ) ^ 2 := by
    have h2 : Real.exp (-(2 * Real.log M)) = 1 / (M : ℝ) ^ 2 := by
      rw [Real.exp_neg, show 2 * Real.log M = Real.log ((M : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]
    rw [← h2]; exact Real.exp_le_exp.mpr (by linarith)
  have hle := le_of_tendsto' hS.tendsto_sum_nat
    (dhpr_partial χ₁ h1 k hσ hσ2 hCT hCH hA0 hMert hHyp _ hv0pos)
  rw [div_le_iff₀ hF]
  refine hle.trans ?_
  exact dhpr_arith k hCT hCD hCH hC1 hC2 hC3 hM0 hℓ1 (Nat.cast_nonneg _) (by linarith) hA0 hA
    (by linarith) (by linarith) hF (Real.exp_pos _).le hexp

theorem deuring_heilbronn_prime_sum : DHPrimeOf := by
  intro hH
  obtain ⟨CH, hCH, hHyp⟩ := hH
  obtain ⟨CD, hCD, hL1⟩ := lfunction_one_le_of_siegel_zero
  obtain ⟨CT, hCT, hMert⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨max (max (30 * CD) (18 * CT + 9)) (110 * CH),
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 18 * CT + 9) (le_max_of_le_left (le_max_right _ _)), ?_⟩
  intro M _ χ₁ β₁ σ k hM h1 hne hz hβ hβ1 hσ hσ2
  exact dhpr_main χ₁ k hM h1 hβ1 hσ hσ2 hCH.le hCD hCT
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _)
    (hL1 M χ₁ β₁ hne hz hβ hβ1) hMert (fun y x hy hyx => hHyp M χ₁ y x hM h1 hne hy hyx)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

