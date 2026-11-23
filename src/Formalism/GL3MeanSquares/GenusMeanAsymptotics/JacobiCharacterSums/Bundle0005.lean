module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0004

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Turan2Main
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem prodLower (n : ℕ) (z : Fin n → ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ξ : ℂ) (hξ : ‖ξ‖ = ρ⁻¹) :
    ρ⁻¹ ^ n * ∏ i, |ρ - ‖z i‖| ≤ ‖∏ i, (1 - z i * ξ)‖ := by
  have hfac : ∀ i, ρ⁻¹ * |ρ - ‖z i‖| ≤ ‖1 - z i * ξ‖ := by
    intro i
    have h1 : ρ⁻¹ * (ρ - ‖z i‖) = 1 - ‖z i‖ * ρ⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hρ.ne']; ring
    have h2 : ρ⁻¹ * |ρ - ‖z i‖| = |1 - ‖z i‖ * ρ⁻¹| := by
      rw [← h1, abs_mul, abs_of_pos (inv_pos.mpr hρ)]
    rw [h2]
    calc |1 - ‖z i‖ * ρ⁻¹| = |‖(1 : ℂ)‖ - ‖z i * ξ‖| := by rw [norm_one, norm_mul, hξ]
      _ ≤ ‖1 - z i * ξ‖ := abs_norm_sub_norm_le _ _
  calc ρ⁻¹ ^ n * ∏ i, |ρ - ‖z i‖| = ∏ i, (ρ⁻¹ * |ρ - ‖z i‖|) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, ‖1 - z i * ξ‖ :=
        Finset.prod_le_prod₀ (fun i _ => mul_nonneg (inv_nonneg.mpr hρ.le) (abs_nonneg _))
          (fun i _ => hfac i)
    _ = ‖∏ i, (1 - z i * ξ)‖ := (norm_prod Finset.univ _).symm

theorem turan2Main (n m : ℕ) (z : Fin n → ℂ) (hn : 1 ≤ n) (hz : ∀ i, ‖z i‖ ≤ 1) (hz1 : ∃ i, ‖z i‖ = 1) :
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + n ∧ ((n : ℝ) / (1600 * ((m : ℝ) + n))) ^ n ≤ ‖∑ i, z i ^ k‖ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hz1
  set B : ℝ := ((n : ℝ) / (1600 * ((m : ℝ) + n))) ^ n with hBdef
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hM : (0 : ℝ) < (m : ℝ) + n := by linarith
  have hnM : (n : ℝ) ≤ (m : ℝ) + n := by linarith
  have hq1 : m + 1 ≤ (m + n) / n * n := by
    have h1 := Nat.div_add_mod (m + n) n
    have h2 := Nat.mod_lt (m + n) (show n > 0 by omega)
    rw [Nat.mul_comm] at h1
    generalize (m + n) / n * n = Q at h1 ⊢
    generalize (m + n) % n = t at h1 h2
    omega
  have hq2 : (((m + n) / n : ℕ) : ℝ) * (n : ℝ) ≤ (m : ℝ) + n := by
    exact_mod_cast Nat.div_mul_le_self (m + n) n
  set q : ℕ := (m + n) / n with hqdef
  set M : ℝ := (m : ℝ) + n with hMdef
  set r : ℝ := (n : ℝ) / (6 * M) with hr
  have hr0 : 0 < r := div_pos (by linarith) (by linarith)
  have hr6 : r ≤ 1 / 6 := by
    rw [hr, div_le_iff₀ (by linarith)]; linarith
  obtain ⟨ρ, hρc, hP⟩ := prodDist (fun i : Fin n => ‖z i‖) Finset.univ (1 - 2 * r) r hr0
  have hP' : (r / 25) ^ n ≤ ∏ j : Fin n, |ρ - ‖z j‖| := by
    have h := hP
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  set P : ℝ := ∏ j : Fin n, |ρ - ‖z j‖| with hPdef
  have hρlo : 1 - 3 * r ≤ ρ := by have := (abs_le.mp hρc).1; linarith
  have hρhi : ρ ≤ 1 - r := by have := (abs_le.mp hρc).2; linarith
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hP0 : 0 < P := lt_of_lt_of_le (pow_pos (div_pos hr0 (by norm_num)) n) hP'
  have hρq : (1 : ℝ) / 2 ≤ ρ ^ q := by
    have hb := one_add_mul_le_pow (a := ρ - 1) (by linarith) q
    have he : 1 + (ρ - 1) = ρ := by ring
    rw [he] at hb
    have h3 : (q : ℝ) * (3 * r) ≤ 1 / 2 := by
      have he2 : (q : ℝ) * (3 * r) = ((q : ℝ) * n) / (2 * M) := by rw [hr]; ring_nf
      rw [he2, div_le_iff₀ (by linarith)]; linarith
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - ρ ≤ 3 * r by linarith) hq0]
  have hρm : (1 / 2 : ℝ) ^ n ≤ ρ ^ (m + 1) := by
    calc (1 / 2 : ℝ) ^ n ≤ (ρ ^ q) ^ n := pow_le_pow_left₀ (by norm_num) hρq n
      _ = ρ ^ (q * n) := (pow_mul ρ q n).symm
      _ ≤ ρ ^ (m + 1) := pow_le_pow_of_le_one hρ0.le hρ1.le hq1
  have hkey : (n : ℝ) * (2 ^ n * B) < ρ ^ (m + 1) * P := by
    have hlow : ((n : ℝ) / (300 * M)) ^ n ≤ ρ ^ (m + 1) * P := by
      calc ((n : ℝ) / (300 * M)) ^ n = (1 / 2 : ℝ) ^ n * (r / 25) ^ n := by
            rw [← mul_pow]; congr 1; rw [hr]; ring_nf
        _ ≤ ρ ^ (m + 1) * P :=
            mul_le_mul hρm hP' (pow_pos (div_pos hr0 (by norm_num)) n).le (pow_pos hρ0 _).le
    have hB : (n : ℝ) * (2 ^ n * B) = n * ((3 / 8 : ℝ) ^ n * ((n : ℝ) / (300 * M)) ^ n) := by
      rw [hBdef, ← mul_pow, ← mul_pow]; congr 2; ring_nf
    have hY : 0 < ((n : ℝ) / (300 * M)) ^ n := pow_pos (div_pos (by linarith) (by linarith)) n
    have hsmall : (n : ℝ) * (3 / 8 : ℝ) ^ n < 1 := by
      have hb := one_add_mul_le_pow (a := (5 / 3 : ℝ)) (by norm_num) n
      have h83 : (1 + 5 / 3 : ℝ) = 8 / 3 := by norm_num
      rw [h83] at hb
      have hone : (3 / 8 : ℝ) ^ n * (8 / 3) ^ n = 1 := by rw [← mul_pow]; norm_num
      have hpos : (0 : ℝ) < (3 / 8) ^ n := pow_pos (by norm_num) n
      nlinarith [mul_le_mul_of_nonneg_left hb hpos.le]
    calc (n : ℝ) * (2 ^ n * B) = n * ((3 / 8 : ℝ) ^ n * ((n : ℝ) / (300 * M)) ^ n) := hB
      _ = (n * (3 / 8 : ℝ) ^ n) * ((n : ℝ) / (300 * M)) ^ n := by ring
      _ < 1 * ((n : ℝ) / (300 * M)) ^ n := mul_lt_mul_of_pos_right hsmall hY
      _ = ((n : ℝ) / (300 * M)) ^ n := one_mul _
      _ ≤ ρ ^ (m + 1) * P := hlow
  set ξ : ℂ := ((ρ⁻¹ : ℝ) : ℂ) with hξdef
  have hξ : ‖ξ‖ = ρ⁻¹ := by
    rw [hξdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0)]
  have hρinv1 : 1 < ρ⁻¹ := by
    have hc : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    nlinarith [inv_pos.mpr hρ0]
  have hzρ : ∀ i, ‖z i‖ * ρ⁻¹ ≠ 1 := by
    intro i h
    have hzi : ‖z i‖ = ρ := by
      have h' : ‖z i‖ * ρ⁻¹ * ρ = 1 * ρ := by rw [h]
      rwa [mul_assoc, inv_mul_cancel₀ hρ0.ne', mul_one, one_mul] at h'
    have hP00 : P = 0 := by
      rw [hPdef]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hzi])
    linarith
  set y : Fin n → ℂ := fun i => z i * ξ with hydef
  have hyn : ∀ i, ‖y i‖ = ‖z i‖ * ρ⁻¹ := fun i => by
    show ‖z i * ξ‖ = _
    rw [norm_mul, hξ]
  have hy : ∀ i, ‖y i‖ ≠ 1 := fun i => by rw [hyn]; exact hzρ i
  have hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ B := fun k h1 h2 => (hcon k h1 h2).le
  have hRP : 0 < ρ ^ (m + 1) * P := mul_pos (pow_pos hρ0 _) hP0
  set K : ℝ := ((n : ℝ) * (2 ^ n * B)) / (ρ ^ (m + 1) * P) with hK
  have hKlt : K < 1 := by rw [hK, div_lt_one hRP]; exact hkey
  have hbound : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ (m + 1) / (1 - y i * ζ)‖ ≤ K := by
    intro ζ hζ
    have hnζ' : ‖ξ * ζ‖ = ρ⁻¹ := by rw [norm_mul, hξ, hζ, mul_one]
    have hsum : ∑ i, (y i * ζ) ^ (m + 1) / (1 - y i * ζ)
        = ∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hyz : y i * ζ = z i * (ξ * ζ) := by
        show z i * ξ * ζ = z i * (ξ * ζ)
        ring
      rw [hyz]
    rw [hsum]
    have hne : ∀ i, 1 - z i * (ξ * ζ) ≠ 0 := by
      intro i h
      have h1 : z i * (ξ * ζ) = 1 := (sub_eq_zero.mp h).symm
      have h2 : ‖z i * (ξ * ζ)‖ = 1 := by rw [h1, norm_one]
      rw [norm_mul, hnζ'] at h2
      exact hzρ i h2
    have hA := prodLower n z ρ hρ0 (ξ * ζ) hnζ'
    have hmain := Tbound n m hn z hz B hβ (ξ * ζ) (by rw [hnζ']; exact hρinv1.le) hne
    rw [hnζ'] at hmain
    have hS0 : 0 ≤ ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ := norm_nonneg _
    have h1 : ρ⁻¹ ^ n * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
        ≤ ρ⁻¹ ^ n * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) := by
      calc ρ⁻¹ ^ n * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
            = (ρ⁻¹ ^ n * P) * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ := by ring
        _ ≤ ‖∏ i, (1 - z i * (ξ * ζ))‖ * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ :=
            mul_le_mul_of_nonneg_right hA hS0
        _ ≤ ρ⁻¹ ^ (m + 1) * (n * (ρ⁻¹ ^ n * (2 ^ n * B))) := hmain
        _ = ρ⁻¹ ^ n * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) := by ring
    have h2 : P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖
        ≤ ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B)) :=
      le_of_mul_le_mul_left h1 (pow_pos (inv_pos.mpr hρ0) n)
    have h3 : ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
        ≤ n * (2 ^ n * B) := by
      calc ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖)
            ≤ ρ ^ (m + 1) * (ρ⁻¹ ^ (m + 1) * (n * (2 ^ n * B))) :=
            mul_le_mul_of_nonneg_left h2 (pow_pos hρ0 _).le
        _ = (ρ * ρ⁻¹) ^ (m + 1) * (n * (2 ^ n * B)) := by rw [mul_pow]; ring
        _ = n * (2 ^ n * B) := by rw [mul_inv_cancel₀ hρ0.ne', one_pow, one_mul]
    rw [hK, le_div_iff₀ hRP]
    calc ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖ * (ρ ^ (m + 1) * P)
          = ρ ^ (m + 1) * (P * ‖∑ i, (z i * (ξ * ζ)) ^ (m + 1) / (1 - z i * (ξ * ζ))‖) := by ring
      _ ≤ n * (2 ^ n * B) := h3
  have hcard := avgLimit y hy (m + 1) (by omega) K hbound
  have hmem : i0 ∈ Finset.univ.filter (fun i => 1 < ‖y i‖) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hyn, hi0, one_mul]
    exact hρinv1
  have hpos : 0 < (Finset.univ.filter (fun i => 1 < ‖y i‖)).card := Finset.card_pos.mpr ⟨i0, hmem⟩
  have hone : (1 : ℝ) ≤ ((Finset.univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) := by exact_mod_cast hpos
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.UbTerms
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem lb_part (a : ℕ) (D : ℝ) (m n j : ℕ) (T : ℝ) (hmj : m ≤ j)
    (hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j)
    (hT : Real.exp (-((a : ℝ) * m) - a * n * D) ≤ T) :
    1 / (E0 a D * (rr a / 8) ^ j) ≤ (1 / 2) ^ j * T := by
  have hR : rr a / 8 = 2 * Real.exp ((a : ℝ) + 1) := by unfold rr; ring
  have hm' : (m : ℝ) ≤ j := by exact_mod_cast hmj
  have ham : (a : ℝ) * m ≤ a * j := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg a)
  have key : Real.exp (-((a : ℝ) * D / eps a ^ 2) - ((a : ℝ) + 1) * j)
      ≤ Real.exp (-((a : ℝ) * m) - a * n * D) := by
    apply Real.exp_le_exp.mpr
    linarith
  have heq : 1 / (E0 a D * (rr a / 8) ^ j)
      = (1 / 2) ^ j * Real.exp (-((a : ℝ) * D / eps a ^ 2) - ((a : ℝ) + 1) * j) := by
    rw [hR, E0, mul_pow, Real.exp_sub, Real.exp_neg, mul_comm ((a : ℝ) + 1) (j : ℝ),
      Real.exp_nat_mul]
    rw [one_div (2 : ℝ)]
    first
    | ring1
    | (field_simp; done)
    | (field_simp; ring1)
    | (field_simp; rw [← mul_pow]; norm_num)
  rw [heq]
  exact (mul_le_mul_of_nonneg_left key (by positivity)).trans
    (mul_le_mul_of_nonneg_left hT (by positivity))

theorem x_part (a : ℕ) (c₁ K : ℝ) (hc₁ : 0 < c₁) (j : ℕ) (hj : (j : ℝ) ≤ 2 * th a * K + j0 a) :
    c₁ * Real.exp (-K) ≤ c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j := by
  have hlog := log_rr_pos a
  have hid := th_log a
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  have hRj : rr a ^ j = Real.exp (j * Real.log (rr a)) := by
    rw [Real.exp_nat_mul, Real.exp_log hRpos]
  rw [hRj, mul_div_assoc, ← Real.exp_sub]
  refine mul_le_mul_of_nonneg_left ?_ hc₁.le
  rw [Real.exp_le_exp]
  have h1 : (j : ℝ) * Real.log (rr a)
      ≤ (2 * th a * K + j0 a) * Real.log (rr a) :=
    mul_le_mul_of_nonneg_right hj hlog.le
  have h2 : (2 * th a * K + j0 a) * Real.log (rr a)
      = K + j0 a * Real.log (rr a) := by
    linear_combination K * hid
  linarith

theorem far_part (a : ℕ) (S : ℝ) (j : ℕ) (hj2 : 2 ≤ j) (hS : S ≤ 1 + j) :
    eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  have hinv : eps a ^ k = 1 / rr a ^ k := by
    unfold eps; rw [one_div_pow]
  have hJ0 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hSX : S ≤ (((k + 2 : ℕ) : ℝ) + 1) ^ 2 := by linarith [sq_nonneg ((k + 2 : ℕ) : ℝ)]
  have e : rr a ^ 2 * (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 2)
      = (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by
    rw [pow_add (rr a) k 2, mul_comm (rr a ^ k) (rr a ^ 2),
      mul_div_mul_left _ _ (pow_ne_zero 2 hRpos.ne')]
  rw [hinv, e, one_div_mul_eq_div]
  gcongr

private theorem pow_mul_div_pow_succ_eq_div (η X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / η ^ (j + 1)) = X / η := by
  first
  | rw [mul_div_assoc', pow_succ η j, mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)

private theorem pow_mul_div_mul_pow_eq_div (η M X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / (M * η ^ j)) = X / M := by
  first
  | rw [mul_div_assoc', mul_comm M (η ^ j), mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)


set_option maxHeartbeats 800000 in
theorem ub_terms (a : ℕ) (CP CF cZ cS c₂ κ L ℓ lam η Mr K : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hCP : 0 < CP) (hCF : 0 < CF) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₂ : 0 < c₂)
    (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam) (hη : 0 < η) (hMr : 0 < Mr) (hK : 0 < K)
    (hlη1 : lam / η ≤ 2 * (lam * L) / cZ) (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hηc : η ≤ c0 a)
    (hηL : η * L < c₂ * K) (h25c : 25 * CF * c₂ ≤ κ) (hκth : κ ≤ th a)
    (hc₂P : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a) (hjr : th a * K < j) :
    η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) ≤
      (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hR16 := rr_gt a
  have hRpos : 0 < rr a := by linarith
  have hRne : rr a ≠ 0 := hRpos.ne'
  have hηne : η ≠ 0 := hη.ne'
  have hL0 : 0 < L := by linarith
  have hJ1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hJpos : (0 : ℝ) < j := by linarith
  have hJsq : (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by linarith [sq_nonneg (j : ℝ)]
  have hL2 : 1 ≤ L ^ 2 := by linarith [mul_le_mul hL hL zero_le_one hL0.le]
  have hLL3 : L ≤ L ^ 3 := by linarith [mul_le_mul_of_nonneg_left hL2 hL0.le]
  have hL3 : 1 ≤ L ^ 3 := by linarith
  have hJ1sq : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := by
    linarith [mul_le_mul_of_nonneg_left hL3 (sq_nonneg ((j : ℝ) + 1)), sq_nonneg (j : ℝ)]
  have hJL : (j : ℝ) * L ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := mul_le_mul hJsq hLL3 hL0.le (by positivity)
  have hℓ2 : ℓ ^ 2 ≤ 4 * L ^ 2 := by
    linarith [mul_le_mul hℓ hℓ hℓ0 (by linarith : (0 : ℝ) ≤ 2 * L)]
  have b1 : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) ≤ 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η = CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (lam / η) := by ring
      _ ≤ CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (2 * (lam * L) / cZ) :=
          mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * ℓ ^ 2 := by ring
      _ ≤ 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * (4 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hℓ2 (by positivity)
      _ = 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b3 : η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) ≤ 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_mul_pow_eq_div η Mr _ hηne j]
    calc CP * ((j : ℝ) + 1) * ℓ ^ 2 / Mr = CP * ((j : ℝ) + 1) * (ℓ ^ 2 / Mr) := by ring
      _ ≤ CP * ((j : ℝ) + 1) * (32 * lam / cS) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 32 * CP / cS * lam * ((j : ℝ) + 1) := by ring
      _ ≤ 32 * CP / cS * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJ1sq (by positivity)
      _ = 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b4 : η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) ≤ 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc 2 * (j : ℝ) * lam / η = 2 * (j : ℝ) * (lam / η) := by ring
      _ ≤ 2 * (j : ℝ) * (2 * (lam * L) / cZ) := mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 4 / cZ * lam * ((j : ℝ) * L) := by ring
      _ ≤ 4 / cZ * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJL (by positivity)
      _ = 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have hx0 : 0 ≤ CP * ℓ * η := by positivity
  have hxK : CP * ℓ * η ≤ 2 * CP * c₂ * K := by
    have e1 : CP * η * ℓ ≤ CP * η * (2 * L) := mul_le_mul_of_nonneg_left hℓ (by positivity)
    have e2 : CP * (η * L) ≤ CP * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCP.le
    linarith
  have hexR : Real.exp 1 * (CP * ℓ * η) * rr a ≤ th a * K := by
    calc Real.exp 1 * (CP * ℓ * η) * rr a
        ≤ Real.exp 1 * (2 * CP * c₂ * K) * rr a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxK (Real.exp_pos 1).le) hRpos.le
      _ = (2 * Real.exp 1 * CP * c₂ * rr a) * K := by ring
      _ ≤ th a * K := mul_le_mul_of_nonneg_right hc₂P hK.le
  have hy : Real.exp 1 * (CP * ℓ * η) / (j : ℝ) ≤ 1 / rr a := by
    first
    | (rw [div_le_div_iff₀ hJpos hRpos]; linarith)
    | (rw [div_le_div_iff hJpos hRpos]; linarith)
    | (rw [div_le_div_iff_of_pos hJpos hRpos]; linarith)
  have b2 : η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    calc η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) = (CP * ℓ * η) ^ j / ((j - 1).factorial : ℝ) := by ring
      _ ≤ (j : ℝ) * (Real.exp 1 * (CP * ℓ * η) / j) ^ j := fact_bound _ hx0 j hj
      _ ≤ (j : ℝ) * (1 / rr a) ^ j := by
          first
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy j) hJpos.le
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left (by positivity) hy j) hJpos.le
          | gcongr (j : ℝ) * ?_ ^ j
      _ = (j : ℝ) / rr a ^ j := by rw [one_div_pow, mul_one_div]
      _ ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by gcongr
  have b5 : η ^ j * (CF * L * 25 ^ j) ≤ rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) := by
    have h25 : 25 * η ≤ 1 / rr a := by
      have := twentyFive_mul_smallConstant a
      linarith
    have hcl : 25 * (CF * η * L) ≤ (j : ℝ) := by
      have e1 : CF * (η * L) ≤ CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCF.le
      have e2 : 25 * CF * c₂ * K ≤ th a * K :=
        mul_le_mul_of_nonneg_right (h25c.trans hκth) hK.le
      linarith
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    calc η ^ (k + 1) * (CF * L * 25 ^ (k + 1)) = 25 * (CF * η * L) * (25 * η) ^ k := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (1 / rr a) ^ k := by
          first
          | exact mul_le_mul hcl (pow_le_pow_left₀ (by positivity) h25 k) (by positivity) (by positivity)
          | exact mul_le_mul hcl (pow_le_pow_left (by positivity) h25 k) (by positivity) (by positivity)
      _ = ((k + 1 : ℕ) : ℝ) / rr a ^ k := by rw [one_div_pow, mul_one_div]
      _ ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by gcongr
      _ = rr a * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 1)) := by
          rw [pow_succ (rr a) k, mul_div_assoc', mul_comm (rr a ^ k) (rr a),
            mul_div_mul_left _ _ hRne]
  have hsplit : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ) + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * (j : ℝ) * lam / η ^ (j + 1) + CF * L * 25 ^ j)
      = η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) + η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) + η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) + η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) + η ^ j * (CF * L * 25 ^ j) := by
    ring
  have hfin : 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + ((j : ℝ) + 1) ^ 2 / rr a ^ j + 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) = (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by ring
  rw [hsplit]
  exact (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5).trans_eq hfin

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

