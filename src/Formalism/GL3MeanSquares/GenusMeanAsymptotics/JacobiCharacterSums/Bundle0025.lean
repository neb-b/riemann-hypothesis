module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0020
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0021
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0022
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0003

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperB
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem charSum_le (hχ : χ ≠ 1) (m : ℕ) : ‖∑ n ∈ Ioc 0 m, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have e : Icc 1 m = Ioc 0 m := by ext x; simp; omega
  have := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ m
  rwa [e] at this

theorem cS_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖DirichletCharacter.LFunction χ 1 - cS χ N‖ ≤ 4 * ((q : ℝ) + 1) / N := by
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) (Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ)
    1 (by simp) N hN
  have e : Icc 1 N = Ioc 0 N := by ext x; simp; omega
  have e2 : ∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) = cS χ N := by
    rw [e, cS]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [e2] at h
  have e3 : (N : ℝ) ^ (-(1 : ℂ).re) = (N : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
  rw [e3] at h
  simp only [norm_one, Complex.one_re, div_one] at h
  calc _ ≤ 2 * ((q : ℝ) + 1) * (1 + 1) * (N : ℝ)⁻¹ := h
    _ = 4 * ((q : ℝ) + 1) / N := by ring

theorem abel_identity (c : ℕ → ℂ) (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, c n * (w n : ℂ) =
      (∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ) +
        ∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih =>
    rw [Finset.sum_Ioc_succ_top hUV, ih, Finset.sum_Ioc_succ_top hUV,
      Finset.sum_Ioc_succ_top (Nat.zero_le V)]
    push_cast
    ring

theorem tele (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, (w n - w (n + 1)) = w (U + 1) - w (V + 1) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih => rw [Finset.sum_Ioc_succ_top hUV, ih]; ring

theorem abel_bound (c : ℕ → ℂ) (w : ℕ → ℝ) (B : ℝ) (hA : ∀ m, ‖∑ n ∈ Ioc 0 m, c n‖ ≤ B)
    (U V : ℕ) (hUV : U ≤ V) (hw0 : 0 ≤ w (U + 1))
    (hw : ∀ n, U < n → 0 ≤ w (n + 1) ∧ w (n + 1) ≤ w n) :
    ‖∑ n ∈ Ioc U V, c n * (w n : ℂ)‖ ≤ 2 * B * w (U + 1) := by
  rw [abel_identity c w U V hUV]
  have hV : 0 ≤ w (V + 1) := by
    rcases hUV.lt_or_eq with h | h
    · exact (hw V h).1
    · rw [← h]; exact hw0
  have h1 : ‖(∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)‖ ≤ B * w (V + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hV]
    exact mul_le_mul_of_nonneg_right (hA V) hV
  have h2 : ‖(∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ)‖ ≤ B * w (U + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hA U) hw0
  have h3 : ‖∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ ≤
      B * (w (U + 1) - w (V + 1)) := by
    calc _ ≤ ∑ n ∈ Ioc U V, ‖(∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc U V, B * (w n - w (n + 1)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' : U < n := (Finset.mem_Ioc.mp hn).1
        have hd : 0 ≤ w n - w (n + 1) := by linarith [(hw n hn').2]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hA n) hd
      _ = B * (w (U + 1) - w (V + 1)) := by rw [← Finset.mul_sum, tele w U V hUV]
  have h4 := norm_add_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
    (∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ))
  have h5 := norm_sub_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)) ((∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
  linarith

def lw (n : ℕ) : ℝ := Real.log n / n

theorem lw_nonneg (n : ℕ) : 0 ≤ lw n :=
  div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

theorem lw_anti (n : ℕ) (hn : 3 ≤ n) : 0 ≤ lw (n + 1) ∧ lw (n + 1) ≤ lw n := by
  refine ⟨lw_nonneg _, ?_⟩
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9; linarith
  unfold lw
  push_cast
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (by linarith)) (by linarith)

theorem cT_sub (U V : ℕ) (hUV : U ≤ V) :
    cT χ V - cT χ U = ∑ n ∈ Ioc U V, χ (n : ZMod q) * (lw n : ℂ) := by
  rw [cT, cT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUV, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold lw; push_cast; ring

theorem cT_diff2 (hχ : χ ≠ 1) (U V : ℕ) (hU : 2 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 2 * ((q : ℝ) + 1) * lw (U + 1) := by
  rw [cT_sub χ U V hUV]
  exact abel_bound (fun n => χ (n : ZMod q)) lw _ (charSum_le χ hχ) U V hUV (lw_nonneg _)
    (fun n hn => lw_anti n (by omega))

theorem cT_diff (hχ : χ ≠ 1) (U V : ℕ) (hU : 1 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 4 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hU0 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hlU : 0 ≤ Real.log ((U : ℝ) + 1) := Real.log_nonneg (by linarith)
  rcases (show 2 ≤ U ∨ U = 1 by omega) with h2 | h1
  · have h := cT_diff2 χ hχ U V h2 hUV
    have e : lw (U + 1) = Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) := by unfold lw; push_cast; rfl
    rw [e] at h
    have : Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hy : 0 ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) := by positivity
    calc _ ≤ _ := h
      _ ≤ 2 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by nlinarith
  · subst h1
    rcases (show V = 1 ∨ 2 ≤ V by omega) with hv | hv
    · subst hv; simp only [sub_self, norm_zero]; positivity
    · have hA := cT_diff2 χ hχ 2 V le_rfl hv
      have hB : ‖cT χ 2 - cT χ 1‖ ≤ 1 / 2 := by
        rw [cT_sub χ 1 2 (by norm_num)]
        have e : Ioc 1 2 = {2} := by decide
        rw [e, Finset.sum_singleton]
        rw [norm_mul, Complex.norm_real]
        have hc : ‖χ ((2 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have hl : ‖lw 2‖ ≤ 1 / 2 := by
          rw [Real.norm_of_nonneg (lw_nonneg 2)]
          unfold lw; push_cast
          have := Real.log_two_lt_d9
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
        calc _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul hc hl (norm_nonneg _) (by norm_num)
          _ = 1 / 2 := by ring
      have hl3 : lw 3 ≤ 2 / 3 := by
        unfold lw; push_cast
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
      have hsplit : cT χ V - cT χ 1 = (cT χ V - cT χ 2) + (cT χ 2 - cT χ 1) := by ring
      rw [hsplit]
      have hl2 : 0 ≤ Real.log ((1 : ℕ) + (1 : ℝ)) := Real.log_nonneg (by norm_num)
      have : (1 : ℝ) ≤ (1 + Real.log ((1 : ℕ) + (1 : ℝ))) / ((1 : ℕ) + (1 : ℝ)) * 2 := by
        push_cast; push_cast at hl2
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
      calc _ ≤ ‖cT χ V - cT χ 2‖ + ‖cT χ 2 - cT χ 1‖ := norm_add_le _ _
        _ ≤ 2 * ((q : ℝ) + 1) * (2 / 3) + 1 / 2 := by
          have : 2 * ((q : ℝ) + 1) * lw (2 + 1) ≤ 2 * ((q : ℝ) + 1) * (2 / 3) :=
            mul_le_mul_of_nonneg_left hl3 (by positivity)
          linarith
        _ ≤ _ := by nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHIneqFA
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

private theorem norm_inv_pow_sub_inv_pow_le (a b : ℂ) (η δ : ℝ) (hη : 0 < η) (ha : η ≤ ‖a‖) (hb : η ≤ ‖b‖)
    (hab : ‖b - a‖ ≤ δ) (n : ℕ) : ‖1 / a ^ n - 1 / b ^ n‖ ≤ n * δ / η ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      linarith
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, norm_zero] at hb
      linarith
    have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hab
    have key : 1 / a ^ (n + 1) - 1 / b ^ (n + 1) =
        (1 / a) * (1 / a ^ n - 1 / b ^ n) + (1 / b ^ n) * ((b - a) / (a * b)) := by
      field_simp
      ring
    rw [key]
    have h1 : ‖1 / a‖ ≤ 1 / η := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hη ha
    have h2 : ‖1 / b ^ n‖ ≤ 1 / η ^ n := by
      rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (pow_pos hη n) (pow_le_pow_left₀ hη.le hb n)
    have h3 : ‖(b - a) / (a * b)‖ ≤ δ / (η * η) := by
      rw [norm_div, norm_mul]
      exact div_le_div₀ hδ hab (mul_pos hη hη) (mul_le_mul ha hb hη.le (norm_nonneg _))
    calc _ ≤ ‖1 / a‖ * ‖1 / a ^ n - 1 / b ^ n‖ + ‖1 / b ^ n‖ * ‖(b - a) / (a * b)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 / η * (n * δ / η ^ (n + 1)) + 1 / η ^ n * (δ / (η * η)) := by gcongr
      _ = _ := by
        push_cast
        field_simp
        ring

theorem dhfShiftPoleN (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (c : Prop) [Decidable c]
    (hc : ¬ c → 1 / 8 ≤ |γ|) (s : ℂ) (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    ‖1 / (s - 1) ^ (k + 1) - (if c then 1 / (s - β₁) ^ (k + 1) else 0)‖ ≤
      ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hre1 : (s - 1).re = η := by
    rw [hs]
    simp
  have hre2 : (s - (β₁ : ℂ)).re = 1 + η - β₁ := by
    rw [hs]
    simp
  have him : (s - 1).im = γ := by
    rw [hs]
    simp
  have hsa : η ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [hre1, abs_of_pos hη] at this
    exact this
  have hsb : η ≤ ‖s - (β₁ : ℂ)‖ := by
    have := Complex.re_le_norm (s - (β₁ : ℂ))
    rw [hre2] at this
    linarith
  have hd : ‖(s - (β₁ : ℂ)) - (s - 1)‖ ≤ 1 - β₁ := by
    have e : (s - (β₁ : ℂ)) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h8 : (0 : ℝ) ≤ 8 ^ (k + 1) := by positivity
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · linarith
    · positivity
  split_ifs with h
  · have := norm_inv_pow_sub_inv_pow_le (s - 1) (s - β₁) η (1 - β₁) hη hsa hsb hd (k + 1)
    push_cast at this
    linarith
  · have hγ : 1 / 8 ≤ |γ| := hc h
    have hs1 : 1 / 8 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [him] at this
      linarith
    rw [sub_zero, norm_div, norm_one, norm_pow]
    have hb : 1 / ‖s - 1‖ ^ (k + 1) ≤ 8 ^ (k + 1) := by
      rw [div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = 8 ^ (k + 1) * (1 / 8) ^ (k + 1) := by
            rw [← mul_pow]
            norm_num
        _ ≤ 8 ^ (k + 1) * ‖s - 1‖ ^ (k + 1) := by gcongr
    linarith

private theorem one_eighth_le_abs_of_not_mem_pole_disc (γ β₁ : ℝ) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1)
    (h : ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25) : 1 / 8 ≤ |γ| := by
  by_contra hlt
  push_neg at hlt
  apply h
  have hg : γ ^ 2 < 1 / 64 := by
    have := abs_lt.mp hlt
    nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

theorem dhfPoles {M : ℕ} (χ₁ χ : DirichletCharacter ℂ M) (hχ₁2 : χ₁ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1)
    (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) [Decidable (χ = 1)] [Decidable (χ * χ₁ = 1)]
    (c3 c4 : Prop) [Decidable c3] [Decidable c4]
    (h3 : χ = χ₁ → ¬ c3 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h4 : χ = 1 → ¬ c4 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h3' : c3 → χ = χ₁) (h4' : c4 → χ = 1) :
    ‖(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0) + (if χ * χ₁ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
      - (if c3 then 1 / (s - β₁) ^ (k + 1) else 0) - (if c4 then 1 / (s - β₁) ^ (k + 1) else 0)‖
      ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
    have : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
      apply div_nonneg
      · apply mul_nonneg
        · positivity
        · linarith
      · positivity
    exact add_nonneg this (by positivity)
  by_cases h1 : χ = 1
  · have h2 : ¬ (χ * χ₁ = 1) := by
      rw [h1, one_mul]
      exact hχ₁1
    have h3n : ¬ c3 := fun h => hχ₁1 ((h3' h).symm.trans h1)
    simp only [if_pos h1, if_neg h2, if_neg h3n, add_zero, sub_zero]
    exact dhfShiftPoleN η γ β₁ hη hβ2 k c4 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h4 h1 h)) s hs
  · by_cases h2 : χ * χ₁ = 1
    · have hχ : χ = χ₁ := by
        have e : χ = χ * χ₁ * χ₁ := by rw [mul_assoc, ← sq, hχ₁2, mul_one]
        rw [e, h2, one_mul]
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_pos h2, if_neg h4n, zero_add, sub_zero]
      exact dhfShiftPoleN η γ β₁ hη hβ2 k c3 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h3 hχ h)) s hs
    · have h3n : ¬ c3 := fun h => h2 (by rw [h3' h, ← sq, hχ₁2])
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_neg h2, if_neg h3n, if_neg h4n, add_zero, sub_zero, norm_zero]
      exact hpos

theorem dhfReNonneg (S : Multiset ℂ) (h : ∀ x ∈ S, 0 < x.re) :
    0 ≤ ((S.map (fun x : ℂ => 1 / x)).sum).re := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
    have ha := h a (Multiset.mem_cons_self a S)
    have h1 : 0 ≤ (1 / a).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg ha.le (Complex.normSq_nonneg a)
    exact add_nonneg h1 (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem dhfEraseSum (Z : Finset ℂ) (m : ℂ → ℕ) (s b : ℂ) (c : Prop) [Decidable c]
    (hb : c → b ∈ dhFam Z m s) (k : ℕ) :
    ((if c then (dhFam Z m s).erase b else dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) - (if c then 1 / b ^ (k + 1) else 0) := by
  have key : ((dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
    unfold dhFam
    rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
    congr 1
    apply Multiset.map_congr rfl
    intro ρ _
    rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    ring
  split_ifs with h
  · rw [← key, ← Multiset.sum_map_erase (hb h)]
    ring
  · rw [key, sub_zero]

theorem dhfNormArith (D3 D4 P3 P4 S3 S4 I3 I4 A B : ℂ) (k : ℕ) (e3 e4 Dom X : ℝ)
    (h3 : ‖D3 - P3 + S3‖ ≤ e3) (h4 : ‖D4 - P4 + S4‖ ≤ e4)
    (hD3 : D3 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * A) (hD4 : D4 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * B)
    (hdom : ‖A + B‖ ≤ Dom) (hP : ‖P3 + P4 - I3 - I4‖ ≤ X) :
    ‖(S3 - I3) + (S4 - I4)‖ ≤ Dom / (k.factorial : ℝ) + X + e3 + e4 := by
  have hnf : ‖(-1 : ℂ) ^ k / (k.factorial : ℂ)‖ = 1 / (k.factorial : ℝ) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hD : ‖D3 + D4‖ ≤ Dom / (k.factorial : ℝ) := by
    rw [hD3, hD4, ← mul_add, norm_mul, hnf, div_mul_eq_mul_div, one_mul]
    gcongr
  have e : (S3 - I3) + (S4 - I4) =
      ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) + (P3 + P4 - I3 - I4) := by ring
  rw [e]
  have n1 := norm_add_le ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) (P3 + P4 - I3 - I4)
  have n2 := norm_sub_le ((D3 - P3 + S3) + (D4 - P4 + S4)) (D3 + D4)
  have n3 := norm_add_le (D3 - P3 + S3) (D4 - P4 + S4)
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeC
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

def dhprF {M : ℕ} (χ₁ : DirichletCharacter ℂ M) (k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n

lemma dhpr_rpow_le {σ : ℝ} (hσ : 1 ≤ σ) {n v : ℕ} (hn : 1 ≤ n) (hv : (v : ℝ) < Real.log n) :
    1 / (n : ℝ) ^ σ ≤ Real.exp (-((σ - 1) * v)) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : Real.exp ((σ - 1) * v) * n ≤ (n : ℝ) ^ σ := by
    have e1 : (n : ℝ) ^ σ = (n : ℝ) ^ (σ - 1) * n := by
      rw [← Real.rpow_add_one hn0.ne']
      ring_nf
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ hn0.le
    rw [Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.le) (sub_nonneg.mpr hσ)]
  have e2 : Real.exp (-((σ - 1) * v)) / n = 1 / (Real.exp ((σ - 1) * v) * n) := by
    rw [Real.exp_neg]
    field_simp
  rw [e2]
  exact one_div_le_one_div_of_le (by positivity) key

lemma dhpr_block {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ : ℝ} (hσ : 1 ≤ σ) (v : ℕ) (B : ℝ)
    (hH : ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤ B) :
    ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n ≤
      2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) * B := by
  have hterm : ∀ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
      dhprF χ₁ k σ n ≤ 2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
        ((∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hgt : Real.exp (v : ℝ) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn.1
    have hle : (n : ℝ) ≤ Real.exp ((v + 1 : ℕ) : ℝ) := (Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hgt
    have hn1 : 1 ≤ n := by
      by_contra hc
      push_neg at hc
      interval_cases n
      simp at hnpos
    have hlogv : (v : ℝ) < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hnpos]
      exact hgt
    have hlog1 : Real.log n ≤ (v : ℝ) + 1 := by
      have h5 := Real.log_le_log hnpos hle
      rw [Real.log_exp] at h5
      push_cast at h5
      linarith
    have hlog0 : 0 ≤ Real.log n := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg v) hlogv)
    have hz := dhpr_r_nonneg χ₁ h1 n
    have hr := dhpr_rpow_le hσ hn1 hlogv
    have hp1 : (Real.log n) ^ (k + 1) ≤ ((v : ℝ) + 1) ^ (k + 1) := pow_le_pow_left₀ hlog0 hlog1 _
    have hq0 : 0 ≤ (Real.log n) ^ (k + 1) := pow_nonneg hlog0 _
    rw [← dhpr_zetaMul_eq_sum]
    calc dhprF χ₁ k σ n ≤ 2 * (Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ :=
          dhpr_term_le_r χ₁ h1 k n σ
      _ = 2 * ((Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re) * (1 / (n : ℝ) ^ σ) := by ring
      _ ≤ 2 * (((v : ℝ) + 1) ^ (k + 1) * (zetaMul χ₁ n).re) * (Real.exp (-((σ - 1) * v)) / n) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp1 hz) (by norm_num)) hr
            (by positivity) (by positivity)
      _ = _ := by ring
  calc _ ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
          ((∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n) := Finset.sum_le_sum hterm
    _ = 2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
          ∑ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
            (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

lemma dhpr_small {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ : ℝ} (hσ : 1 ≤ σ) (v0 : ℕ) (hv0 : 1 ≤ v0) {CT : ℝ} (hCT : 0 ≤ CT)
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y) :
    ∑ n ∈ Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * CT * (v0 : ℝ) ^ (k + 1) := by
  have hy : (2 : ℝ) ≤ Real.exp (v0 : ℝ) := by
    have hv1 : (1 : ℝ) ≤ v0 := by exact_mod_cast hv0
    calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp v0 := Real.exp_le_exp.mpr hv1
  have hM := hMert _ hy
  rw [Real.log_exp] at hM
  have hIoc : Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊ = Finset.Icc 1 ⌊Real.exp (v0 : ℝ)⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * (v0 : ℝ) ^ k * (Λ n / n) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlog : Real.log n ≤ v0 := by
      have hnle : (n : ℝ) ≤ Real.exp v0 := (Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2
      calc Real.log n ≤ Real.log (Real.exp v0) := Real.log_le_log (by linarith) hnle
        _ = v0 := Real.log_exp _
    have hΛ : 0 ≤ (Λ n : ℝ) / (n : ℝ) := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    calc dhprF χ₁ k σ n ≤ 2 * (Real.log n) ^ k * (Λ n / n) := dhpr_term_le_small χ₁ h1 k n hσ
      _ ≤ 2 * (v0 : ℝ) ^ k * (Λ n / n) := by gcongr
  calc ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, 2 * (v0 : ℝ) ^ k * (Λ n / n) := Finset.sum_le_sum hterm
    _ = 2 * (v0 : ℝ) ^ k * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (v0 : ℝ)⌋₊, Λ n / n := by rw [← Finset.mul_sum, hIoc]
    _ ≤ 2 * (v0 : ℝ) ^ k * (CT * v0) := by gcongr
    _ = 2 * CT * (v0 : ℝ) ^ (k + 1) := by ring

lemma dhpr_hyper_simp (A CH x : ℝ) (v : ℕ) :
    A * Real.log (Real.exp ((v + 1 : ℕ) : ℝ) / Real.exp (v : ℝ))
      + CH * x * (Real.log (Real.exp (v : ℝ)) + 1) / Real.sqrt (Real.exp (v : ℝ)) =
      A + CH * x * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
  have h1 : Real.log (Real.exp ((v + 1 : ℕ) : ℝ) / Real.exp (v : ℝ)) = 1 := by
    rw [← Real.exp_sub, Real.log_exp]
    push_cast
    ring
  have h2 : Real.sqrt (Real.exp (v : ℝ)) = Real.exp ((v : ℝ) / 2) := by
    rw [show Real.exp (v : ℝ) = Real.exp ((v : ℝ) / 2) * Real.exp ((v : ℝ) / 2) by
      rw [← Real.exp_add]; ring_nf, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [h1, Real.log_exp, h2, Real.exp_neg]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

