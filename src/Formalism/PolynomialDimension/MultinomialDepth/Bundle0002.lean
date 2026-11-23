module

public import Formalism.PolynomialDimension.Bundle0002

@[expose] public section

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.FrameMultinomialBoundHolds
section
noncomputable section

open scoped BigOperators
open Finset Real

namespace Formalism.CountingSumsFrames

theorem gram_weylDim_cons (n : ℕ) (A : ℤ) (μ : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons A μ : Fin (n + 1) → ℤ) =
      (∏ j : Fin n, ((((A - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n μ := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, lt_self_iff_false, if_false, one_mul, Fin.succ_pos, if_true,
      Fin.val_succ, Fin.val_zero]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    ring
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_succ, Fin.cons_zero, Fin.not_lt_zero, if_false, one_mul, Fin.succ_lt_succ_iff,
      Fin.val_succ]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl

theorem gram_choose_prod (a' : ℕ) : ∀ n : ℕ,
    (((a' + n).choose n : ℕ) : ℝ) = ∏ j : Fin n, ((a' : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    have h := Nat.add_one_mul_choose_eq (a' + n) n
    have h' : ((a' + n : ℝ) + 1) * (((a' + n).choose n : ℕ) : ℝ) =
        (((a' + n + 1).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast h
    rw [show a' + (n + 1) = a' + n + 1 by ring]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [mul_div_assoc', eq_div_iff hn.ne']
    linarith

theorem gram_prod_le (m : ℕ) (f g : Fin m → ℝ) (t : ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ (1 + t) * g j) :
    ∏ j, f j ≤ (1 + t) ^ m * ∏ j, g j := by
  calc ∏ j, f j ≤ ∏ j, ((1 + t) * g j) := Finset.prod_le_prod₀ (fun j _ => hf j) (fun j _ => hfg j)
    _ = (1 + t) ^ m * ∏ j, g j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem gram_key (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : (n : ℝ) * x ≤ y) :
    (1 - y) * (1 + x) ^ n ≤ 1 := by
  have hp : 0 ≤ (1 + x) ^ n := by positivity
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    have e1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have e2 : (1 + x) ^ n ≤ Real.exp (n * x) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
    calc (1 - y) * (1 + x) ^ n ≤ Real.exp (-y) * Real.exp (n * x) :=
          mul_le_mul e1 e2 hp (Real.exp_pos _).le
      _ = Real.exp (n * x - y) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero

theorem gram_weylDim_pos (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by
  unfold weylDim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with h
  · have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)
    have h2 : μ j ≤ μ i := hμ h.le
    have h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ) := by exact_mod_cast h2
    push_cast
    apply div_pos <;> linarith
  · exact one_pos

theorem one_sub_mul_mul_le (y P W C x : ℝ) (n : ℕ) (hW : 0 ≤ W) (hP0 : 0 ≤ P) (hC : 0 ≤ C)
    (hPle : P ≤ (1 + x) ^ n * C) (hkey : (1 - y) * (1 + x) ^ n ≤ 1) : (1 - y) * (P * W) ≤ C * W := by
  have hPW : 0 ≤ P * W := mul_nonneg hP0 hW
  have hCW : 0 ≤ C * W := mul_nonneg hC hW
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    calc (1 - y) * (P * W) ≤ (1 - y) * (((1 + x) ^ n * C) * W) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPle hW) h.le
      _ = ((1 - y) * (1 + x) ^ n) * (C * W) := by ring
      _ ≤ 1 * (C * W) := mul_le_mul_of_nonneg_right hkey hCW
      _ = C * W := one_mul _

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.HarmonicLevelCountRec
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma dimPol_mono (k' : ℕ) {a b : ℕ} (h : a ≤ b) : dimPol k' a ≤ dimPol k' b :=
  Nat.choose_le_choose k' (by omega)

theorem harmonic_level_count_rec (k' : ℕ) : ∀ A B : ℕ,
    ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B
  | 0, B => by simp [dimHar]
  | A + 1, 0 => by simp [dimHar]
  | A + 1, B + 1 => by
    rw [show min (A + 1) (B + 1) + 1 = (min A B + 1) + 1 by omega, Finset.sum_range_succ']
    have e : ∀ j ∈ range (min A B + 1),
        dimHar k' (A + 1 - (j + 1)) (B + 1 - (j + 1)) = dimHar k' (A - j) (B - j) := by
      intro j _
      rw [show A + 1 - (j + 1) = A - j by omega, show B + 1 - (j + 1) = B - j by omega]
    rw [Finset.sum_congr rfl e, harmonic_level_count_rec k' A B]
    have hle : dimPol k' A * dimPol k' B ≤ dimPol k' (A + 1) * dimPol k' (B + 1) :=
      Nat.mul_le_mul (dimPol_mono k' (by omega)) (dimPol_mono k' (by omega))
    simp only [dimHar, Nat.sub_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, or_self, if_false]
    exact Nat.add_sub_cancel' hle

theorem harmonic_level_count : LevelCount :=
  fun k' A B => harmonic_level_count_rec k' A B

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.WeylDimPosOfAntitone
section
open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem weylDim_cons_snoc (m : ℕ) (a b : ℤ) (μ : Fin m → ℤ) :
    weylDim (m + 2) (Fin.cons a (Fin.snoc μ b) : Fin (m + 2) → ℤ) =
      weylDim m μ * (∏ j : Fin m, ((((a - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) *
      (∏ j : Fin m, ((((μ j - b : ℤ)) : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) *
      (((((a - b : ℤ)) : ℚ) + (m : ℚ) + 1) / ((m : ℚ) + 1)) := by
  unfold weylDim
  simp only [Fin.prod_univ_succ (n := m + 1)]
  simp only [Fin.prod_univ_castSucc (n := m)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last, lt_self_iff_false,
    Fin.not_lt_zero, if_false, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Fin.val_zero, one_mul, mul_one]
  have hl : ∀ x : Fin m, ¬ (Fin.last m < x.castSucc) := fun x => (Fin.castSucc_lt_last x).asymm
  simp only [hl, if_false, Finset.prod_const_one, mul_one]
  push_cast
  simp only [sub_zero, ← add_assoc, add_sub_add_right_eq_sub, Finset.prod_mul_distrib]
  ring

theorem weylDim_zero (m : ℕ) : weylDim m (fun _ => (0 : ℤ)) = 1 := by
  unfold weylDim
  apply Finset.prod_eq_one; intro i _
  apply Finset.prod_eq_one; intro j _
  split_ifs with h
  · have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
      have : (i : ℕ) < (j : ℕ) := h
      have : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast this
      linarith
    simp [this]
  · rfl

theorem weylDim_pos_of_antitone (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by
  unfold weylDim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with h
  · have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)
    have h2 : μ j ≤ μ i := hμ h.le
    have h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ) := by exact_mod_cast h2
    push_cast
    apply div_pos <;> linarith
  · exact one_pos

theorem weylDim_hwt (m A B : ℕ) : (weylDim (m + 2) (hwt m A B) : ℝ) =
    (∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold hwt
  rw [weylDim_cons_snoc, weylDim_zero]
  push_cast
  simp only [sub_zero, sub_neg_eq_add, one_mul, zero_add]

theorem weylDim_cwt (m A c B : ℕ) (μ : Fin m → ℤ) : (weylDim (m + 2) (cwt m A c B μ) : ℝ) =
    (weylDim m μ : ℝ) *
    (∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold cwt
  rw [weylDim_cons_snoc]
  push_cast
  simp only [sub_neg_eq_add]

theorem prod_le_pow_mul_prod (m : ℕ) (f g : Fin m → ℝ) (t : ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ (1 + t) * g j) :
    ∏ j, f j ≤ (1 + t) ^ m * ∏ j, g j := by
  calc ∏ j, f j ≤ ∏ j, ((1 + t) * g j) := Finset.prod_le_prod₀ (fun j _ => hf j) (fun j _ => hfg j)
    _ = (1 + t) ^ m * ∏ j, g j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem fin_sub_pos (m : ℕ) (j : Fin m) : 0 < (m : ℝ) - ((j : ℕ) : ℝ) := by
  have : ((j : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast j.isLt
  linarith

theorem cwt_bound (m A c B : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) (h0 : ∀ i, 0 ≤ μ i ∧ μ i ≤ c)
    (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    0 ≤ (weylDim (m + 2) (cwt m A c B μ) : ℝ) ∧
    (weylDim (m + 2) (cwt m A c B μ) : ℝ) ≤
      (1 + t) ^ (2 * m + 1) * ((weylDim m μ : ℝ) * (weylDim (m + 2) (hwt m A B) : ℝ)) := by
  have hW : 0 < (weylDim m μ : ℝ) := by exact_mod_cast weylDim_pos_of_antitone m μ hμ
  have hμ0 : ∀ j, (0 : ℝ) ≤ (μ j : ℝ) := fun j => by exact_mod_cast (h0 j).1
  have hμc : ∀ j, (μ j : ℝ) ≤ (c : ℝ) := fun j => by exact_mod_cast (h0 j).2
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [weylDim_cwt, weylDim_hwt]
  have f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
    intro j
    have := hμc j
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    apply div_nonneg
    · linarith
    · positivity
  have f2 : ∀ j : Fin m, 0 ≤ ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := by
    intro j; have := fin_sub_pos m j; have := hμ0 j; apply div_nonneg <;> linarith
  have f3 : 0 ≤ ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) := by positivity
  have P1 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := hμ0 j
      have : 0 ≤ t * (((j : ℕ) : ℝ) + 1) := by positivity
      nlinarith)
  have P2 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (fin_sub_pos m j).le
      have := hμc j
      have := fin_sub_pos m j
      have : 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ)) := by positivity
      nlinarith)
  have P3 : ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ t * ((B : ℝ) + m + 1) := by positivity
    nlinarith
  have g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => f1 j
  have g2 : 0 ≤ ∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => f2 j
  have k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => by positivity
  have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have k3 : 0 ≤ (1 + t) ^ m := by positivity
  refine ⟨by positivity, ?_⟩
  calc _ ≤ (weylDim m μ : ℝ) *
        ((1 + t) ^ m * ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
        ((1 + t) ^ m * ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
        ((1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring

theorem hwt_bound (m A c B : ℕ) (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    (weylDim (m + 2) (hwt m (A + c) (B + c)) : ℝ) ≤ (1 + t) ^ (2 * m + 1) * (weylDim (m + 2) (hwt m A B) : ℝ) := by
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [weylDim_hwt, weylDim_hwt]
  push_cast
  have f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := fun j => by positivity
  have f2 : ∀ j : Fin m, 0 ≤ ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := by
    intro j; have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have P1 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ t * (((j : ℕ) : ℝ) + 1) := by positivity
      nlinarith)
  have P2 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (fin_sub_pos m j).le
      have := fin_sub_pos m j
      have : 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ)) := by positivity
      nlinarith)
  have P3 : ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ t * ((m : ℝ) + 1) := by positivity
    nlinarith
  have g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => f1 j
  have g2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => f2 j
  have f3 : 0 ≤ ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) := by positivity
  have k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => by positivity
  have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have k3 : 0 ≤ (1 + t) ^ m := by positivity
  calc _ ≤ ((1 + t) ^ m * ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
        ((1 + t) ^ m * ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
        ((1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring

end Formalism.CountingSumsFrames
end

