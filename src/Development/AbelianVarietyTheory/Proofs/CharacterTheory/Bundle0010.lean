module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythree
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

private theorem sum_range_63_primitiveRoot_pow_eq_ite (ω : ℂ) (hω : IsPrimitiveRoot ω 63) (n : ℕ) :
    ∑ j ∈ Finset.range 63, ω ^ (j * n) = if 63 ∣ n then (63 : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, ω ^ (j * n) = (ω ^ n) ^ j := fun j => by rw [← pow_mul, mul_comm]
  simp_rw [hpow]
  split_ifs with hn
  · rw [(hω.pow_eq_one_iff_dvd n).mpr hn]
    simp
  · have hne : ω ^ n ≠ 1 := fun h => hn ((hω.pow_eq_one_iff_dvd n).mp h)
    have h63 : (ω ^ n) ^ 63 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hg := geom_sum_mul (ω ^ n) 63
    rw [h63, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)

theorem fourier_inv_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63) (m : ℕ)
    (hm : m < 63) :
    ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = 63 * (c m : ℂ) := by
  have hsum := sum_range_63_primitiveRoot_pow_eq_ite ω hω
  calc ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = ∑ k ∈ Finset.range 63, (c k : ℂ) * ∑ j ∈ Finset.range 63, ω ^ (j * (k + 62 * m)) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_add, pow_add]
        ring
    _ = ∑ k ∈ Finset.range 63, (c k : ℂ) * (if 63 ∣ k + 62 * m then (63 : ℂ) else 0) := by
        simp_rw [hsum]
    _ = 63 * (c m : ℂ) := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (by omega)]
          ring
        · intro k hk hkm
          have hk' := Finset.mem_range.mp hk
          rw [if_neg (by omega)]
          simp
        · intro hm'
          exact absurd (Finset.mem_range.mpr hm) hm'

theorem mixed_diff_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (m : ℕ) (hm : m < 53) :
    c (m + 10) - c (m + 3) = c (m + 7) - c m := by
  have key : ∀ n, n < 63 → (63 : ℂ) * (c n : ℂ) = ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n)) :=
    fun n hn => (fourier_inv_sixtythree ω c hω n hn).symm
  have hz : ∑ j ∈ Finset.range 63,
      ((∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 10)))
        - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 3)))
        - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 7)))
        + (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases h21 : 21 ∣ j
    · have hB : ω ^ (186 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
      rw [show j * (62 * (m + 10)) = j * (62 * (m + 7)) + 186 * j by ring,
        show j * (62 * (m + 3)) = j * (62 * m) + 186 * j by ring, pow_add, pow_add, hB]
      ring
    · by_cases h9 : 9 ∣ j
      · have hB : ω ^ (434 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
        rw [show j * (62 * (m + 10)) = j * (62 * (m + 3)) + 434 * j by ring,
          show j * (62 * (m + 7)) = j * (62 * m) + 434 * j by ring, pow_add, pow_add, hB]
        ring
      · rw [h j hj' h21 h9]
        ring
  have h63 : (63 : ℂ) * ((c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m) = 0 := by
    rw [mul_add, mul_sub, mul_sub, key (m + 10) (by omega), key (m + 3) (by omega),
      key (m + 7) (by omega), key m (by omega), ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact hz
  have h' : (c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m = 0 :=
    (mul_eq_zero.mp h63).resolve_left (by norm_num)
  have h'' : ((c (m + 10) - c (m + 3) - c (m + 7) + c m : ℤ) : ℂ) = 0 := by
    push_cast
    exact h'
  have h3 := Int.cast_eq_zero.mp h''
  linarith

private theorem apply_add_21_eq_of_fourier_vanish_order_63 (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (n : ℕ) (hn : n < 42) :
    c (n + 21) = c n := by
  have hs : ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (n + 21)))
      = ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    by_cases h3 : 3 ∣ j
    · have hB : ω ^ (1302 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
      rw [show j * (62 * (n + 21)) = j * (62 * n) + 1302 * j by ring, pow_add, hB, mul_one]
    · rw [h j hj' (by omega) (by omega), zero_mul, zero_mul]
  have e1 := fourier_inv_sixtythree ω c hω (n + 21) (by omega)
  rw [hs, fourier_inv_sixtythree ω c hω n (by omega)] at e1
  have e2 : ((c (n + 21) : ℤ) : ℂ) = (c n : ℂ) :=
    (mul_left_cancel₀ (by norm_num : (63 : ℂ) ≠ 0) e1).symm
  exact_mod_cast e2

theorem no_norm_twelve_order_sixtythree : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 →
    ∑ k ∈ Finset.range 63, c k ^ 2 = 12 →
    (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hnorm hF
  have hrel := fun m (hm : m < 53) => mixed_diff_sixtythree ω c hω hF m hm
  have hper := fun n (hn : n < 42) => apply_add_21_eq_of_fourier_vanish_order_63 ω c hω hF n hn
  have hD : ∀ m, m < 56 → c (m + 7) - c m = c (m % 3 + 7) - c (m % 3) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases h3 : m < 3
      · rw [Nat.mod_eq_of_lt h3]
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
        have e1 := hrel m' (by omega)
        have e2 := ih m' (by omega) (by omega)
        rw [show (m' + 3) % 3 = m' % 3 by omega, show m' + 3 + 7 = m' + 10 by omega]
        linarith
  have hS : ∑ k ∈ Finset.range 63, c k ^ 2 = 3 * ∑ k ∈ Finset.range 21, c k ^ 2 := by
    rw [show (63 : ℕ) = 21 + 21 + 21 from rfl, Finset.sum_range_add, Finset.sum_range_add]
    have h1 : ∑ x ∈ Finset.range 21, c (21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        rw [add_comm, hper x (by have := Finset.mem_range.mp hx; omega)]
    have h2 : ∑ x ∈ Finset.range 21, c (21 + 21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        have hx' := Finset.mem_range.mp hx
        rw [show 21 + 21 + x = x + 21 + 21 by omega, hper (x + 21) (by omega), hper x (by omega)]
    rw [h1, h2]
    ring
  have hcolsum : ∑ k ∈ Finset.range 21, c k ^ 2 =
      ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    rw [show (21 : ℕ) = 7 + 7 + 7 from rfl, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : ∑ x ∈ Finset.range 7, c (7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 7) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [add_comm]
    have h2 : ∑ x ∈ Finset.range 7, c (7 + 7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 14) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [show 7 + 7 + x = x + 14 by omega]
    rw [h1, h2]
  have hcol : ∀ b, b < 7 → (c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2 ≤
      3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    have e3 := hD (b + 14) (by omega)
    have p := hper b (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [show b + 14 + 7 = b + 21 by omega, p] at e3
    have key : (c (b + 7) - c b) ^ 2 + (c (b + 14) - c (b + 7)) ^ 2 + (c b - c (b + 14)) ^ 2 ≤
        3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
      nlinarith [sq_nonneg (c b + c (b + 7) + c (b + 14))]
    rw [e1, e2, e3] at key
    have hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hb3 with h | h | h
    · rw [show (b + 7) % 3 = 1 by omega, show (b + 14) % 3 = 2 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 2 by omega, show (b + 14) % 3 = 0 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 0 by omega, show (b + 14) % 3 = 1 by omega, h] at key
      norm_num at key
      linarith
  rw [hS] at hnorm
  have hS21 : ∑ k ∈ Finset.range 21, c k ^ 2 = 4 := by omega
  have hΔ : 7 * ((c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2) ≤ 12 := by
    have hle := Finset.sum_le_sum (s := Finset.range 7) fun b hb => hcol b (Finset.mem_range.mp hb)
    rw [← Finset.mul_sum, ← hcolsum, hS21] at hle
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    push_cast at hle
    linarith
  have hsum0 : (c 7 - c 0) + (c 8 - c 1) + (c 9 - c 2) = 0 := by
    have e2 := hD 7 (by omega)
    have e3 := hD 14 (by omega)
    have p := hper 0 (by omega)
    norm_num at e2 e3 p
    linarith
  have hzero : c 7 - c 0 = 0 ∧ c 8 - c 1 = 0 ∧ c 9 - c 2 = 0 := by
    generalize c 7 - c 0 = x at hΔ hsum0 ⊢
    generalize c 8 - c 1 = y at hΔ hsum0 ⊢
    generalize c 9 - c 2 = z at hΔ hsum0 ⊢
    have hz : z = -x - y := by linarith
    subst hz
    have h14 : 14 * (x ^ 2 + x * y + y ^ 2) ≤ 12 := by nlinarith
    have hq : x ^ 2 + x * y + y ^ 2 ≤ 0 := by omega
    have hy2 : y ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2 * x + y)]
    have hy : y = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hy2 (sq_nonneg y))
    subst hy
    have hx2 : x ^ 2 ≤ 0 := by nlinarith
    have hx : x = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hx2 (sq_nonneg x))
    subst hx
    norm_num
  have hp7 : ∀ r, r < 3 → c (r + 7) = c r := by
    intro r hr
    interval_cases r <;> norm_num <;> omega
  have hcolc : ∀ b, b < 7 → c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2 = 3 * c b ^ 2 := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [hp7 (b % 3) (Nat.mod_lt _ (by norm_num))] at e1
    rw [hp7 ((b + 7) % 3) (Nat.mod_lt _ (by norm_num))] at e2
    have h1 : c (b + 7) = c b := by linarith
    have h2 : c (b + 14) = c b := by linarith
    rw [h1, h2]
    ring
  have h3 : ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) =
      3 * ∑ b ∈ Finset.range 7, c b ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => hcolc b (Finset.mem_range.mp hb)
  rw [hcolsum, h3] at hS21
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParsevalBoundIntegerVectorSmallFourierSupport
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem parsevalSep_orth (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) (k l : ℕ)
    (hk : k < N) (hl : l < N) :
    ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l)
      = if k = l then (N : ℂ) else 0 := by
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have h0 : ω ≠ 0 := hω.ne_zero hN.ne'
  rw [← Complex.inv_eq_conj h1]
  have hz : ∀ j : ℕ, ω ^ (j * k) * (ω⁻¹) ^ (j * l) = (ω ^ k * (ω ^ l)⁻¹) ^ j := by
    intro j
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]
  simp_rw [hz]
  split_ifs with h
  · subst h
    simp [mul_inv_cancel₀ (pow_ne_zero k h0)]
  · have hne : ω ^ k * (ω ^ l)⁻¹ ≠ 1 := by
      intro h'
      apply h
      apply hω.pow_inj hk hl
      field_simp at h'
      exact h'
    have hp : (ω ^ k * (ω ^ l)⁻¹) ^ N = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    rw [geom_sum_eq hne, hp]
    simp

theorem parsevalSep_identity (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N)
    (c : ℕ → ℤ) :
    ∑ j ∈ Finset.range N, ‖∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k)‖ ^ 2
      = (N : ℝ) * ((∑ k ∈ Finset.range N, c k ^ 2 : ℤ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, map_pow, map_intCast]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  have : ∀ l ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
      = if k = l then (c k : ℂ) * c l * N else 0 := by
    intro l hl
    have := parsevalSep_orth N ω hN hω k l (Finset.mem_range.1 hk) (Finset.mem_range.1 hl)
    have e : ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
       = (c k : ℂ) * c l * ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, this]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hk]
  ring

theorem parsevalSep_bound : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  intro n N ω c S hn hN hω h2 h0 hS
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hP := parsevalSep_identity N ω hN hω c
  rw [h2] at hP
  set F : ℕ → ℂ := fun j => ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) with hF
  have hb : ∀ j, ‖F j‖ ≤ 2 * n := by
    intro j
    have h2' : ∑ k ∈ Finset.range N, (c k : ℝ) ^ 2 = 2 * n := by exact_mod_cast h2
    rw [← h2']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, h1, one_pow, mul_one, Complex.norm_intCast]
    have : |c k| ≤ c k ^ 2 := by
      rw [← sq_abs]
      have := abs_nonneg (c k)
      nlinarith [Int.le_self_sq |c k|]
    exact_mod_cast this
  have hz : ‖F 0‖ ≤ (n : ℝ) - 1 := by
    have : F 0 = ((∑ k ∈ Finset.range N, c k : ℤ) : ℂ) := by simp [hF]
    rw [this, Complex.norm_intCast]
    exact_mod_cast h0
  have hle : ∀ j ∈ Finset.range N, ‖F j‖ ^ 2 ≤
      (if j = 0 then ((n : ℝ) - 1) ^ 2 else 0) + (if j ∈ S then 4 * (n : ℝ) ^ 2 else 0) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      have : ‖F 0‖ ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      rw [if_pos rfl]
      split_ifs
      · have : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
        linarith
      · linarith
    · rw [if_neg hj0, zero_add]
      split_ifs with hjS
      · have := pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
        linarith [show (2 * (n : ℝ)) ^ 2 = 4 * (n : ℝ) ^ 2 by ring]
      · have : F j = 0 := hS j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj) hjS
        simp [this]
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hN),
    Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((Finset.range N ∩ S).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hP' : ∑ j ∈ Finset.range N, ‖F j‖ ^ 2 = (N : ℝ) * (2 * n) := by
    rw [hP]; push_cast; ring
  have key : (2 * n * N : ℝ) ≤ ((n : ℝ) - 1) ^ 2 + 4 * (n : ℝ) ^ 2 * S.card := by
    have : ((Finset.range N ∩ S).card : ℝ) * (4 * (n : ℝ) ^ 2) ≤ S.card * (4 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [← hn1] at key
  exact_mod_cast key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimaryEndomorphismCyclicDecompositionFinrankKer
section
open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL

theorem finrank_ker_lsmul_pow_quotient {F : Type} [Field F] (f : F[X]) (hf : f ≠ 0) (e j : ℕ) :
    Module.finrank F (LinearMap.ker
      ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)) =
      f.natDegree * min j e := by
  have hle : Ideal.span {f ^ e} ≤ Ideal.span {f ^ min j e} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow f (min_le_right j e))
  haveI : Module.Finite F (F[X] ⧸ Ideal.span {f ^ e}) :=
    (AdjoinRoot.powerBasis (pow_ne_zero e hf)).finite
  let π := (Ideal.Quotient.factorₐ F hle).toLinearMap
  have hπ : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact Ideal.Quotient.factor_surjective hle
  have hker : LinearMap.ker π = LinearMap.range
      ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : π (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl
    have h2 : ∀ y : F[X],
        ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)
          (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (f ^ j * y) := fun y => rfl
    rw [LinearMap.mem_ker, h1, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      LinearMap.mem_range]
    constructor
    · rintro ⟨c, rfl⟩
      rcases le_total j e with h | h
      · exact ⟨Ideal.Quotient.mk _ c, by rw [h2, min_eq_left h]⟩
      · refine ⟨0, ?_⟩
        rw [map_zero, min_eq_right h, eq_comm, Ideal.Quotient.eq_zero_iff_mem,
          Ideal.mem_span_singleton]
        exact dvd_mul_right _ _
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [h2, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
      have h3 : f ^ min j e ∣ f ^ j * y - x := (pow_dvd_pow f (min_le_right j e)).trans hy
      have h4 : f ^ min j e ∣ f ^ j * y := (pow_dvd_pow f (min_le_left j e)).mul_right y
      simpa using dvd_sub h4 h3
  have h1 := LinearMap.finrank_range_add_finrank_ker π
  have h2 := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)
  rw [hπ, hker, finrank_top, finrank_quotient_span_eq_natDegree, natDegree_pow] at h1
  rw [mul_comm]
  omega

def piDropTrivial {R : Type} [Ring R] {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (P : ι → Prop) [DecidablePred P] (h : ∀ i, ¬ P i → Subsingleton (M i)) :
    ((i : ι) → M i) ≃ₗ[R] ((i : {i // P i}) → M i) where
  toFun x i := x i
  invFun y i := if hi : P i then y ⟨i, hi⟩ else 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    by_cases hi : P i
    · simp [hi]
    · haveI := h i hi
      exact Subsingleton.elim _ _
  right_inv y := by
    funext i
    simp [i.2]

def kerAevalEquivPi {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (g : Module.End F V)
    {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
    [∀ i, Module F[X] (M i)] [∀ i, IsScalarTower F F[X] (M i)]
    (φ : Module.AEval' g ≃ₗ[F[X]] ((i : ι) → M i)) (p : F[X]) :
    LinearMap.ker (aeval g p) ≃ₗ[F]
      ((i : ι) → LinearMap.ker ((LinearMap.lsmul F[X] (M i) p).restrictScalars F)) where
  toFun x i := ⟨φ (Module.AEval'.of g x) i, by
    have hx : aeval g p • (x : V) = 0 := x.2
    have : p • φ (Module.AEval'.of g x) = 0 := by
      rw [← map_smul, ← Module.AEval.of_aeval_smul, hx, map_zero, map_zero]
    exact congrFun this i⟩
  invFun y := ⟨(Module.AEval'.of g).symm (φ.symm fun i => y i), by
    have : p • (fun i => (y i : M i)) = 0 := funext fun i => (y i).2
    change aeval g p • (Module.AEval'.of g).symm (φ.symm fun i => (y i : M i)) = 0
    rw [← Module.AEval.of_symm_smul, ← map_smul, this, map_zero, map_zero]⟩
  map_add' x y := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g ((x : V) + y)) i =
      φ (Module.AEval'.of g x) i + φ (Module.AEval'.of g y) i
    rw [map_add (f := _), map_add (f := _), Pi.add_apply]
  map_smul' c x := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g (c • (x : V))) i = c • φ (Module.AEval'.of g x) i
    rw [map_smul, LinearMapClass.map_smul_of_tower φ, Pi.smul_apply]
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    funext i
    apply Subtype.ext
    simp

theorem primary_structure : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ Nonempty (Module.AEval' g ≃ₗ[F[X]] ((i : Fin d) → F[X] ⧸ Ideal.span {f ^ e i})) ∧ ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = f.natDegree * ∑ i, min j (e i) := by
  intro F _ V _ _ _ g f m hf hm
  classical
  have hT : Module.IsTorsion' (Module.AEval' g) (Submonoid.powers f) := by
    rw [Submodule.isTorsion'_powers_iff]
    intro x
    refine ⟨m, ?_⟩
    apply (Module.AEval'.of g).symm.injective
    rw [Module.AEval.of_symm_smul, hm, zero_smul, map_zero]
  obtain ⟨d, k, ⟨φ⟩⟩ := Module.torsion_by_prime_power_decomposition hf hT
  let σ := Fintype.equivFin {i : Fin d // 0 < k i}
  let ψ : Module.AEval' g ≃ₗ[F[X]]
      ((i : Fin (Fintype.card {i : Fin d // 0 < k i})) → F[X] ⧸ Ideal.span {f ^ k (σ.symm i)}) :=
    φ ≪≫ₗ DirectSum.linearEquivFunOnFintype F[X] (Fin d) (fun i => F[X] ⧸ Ideal.span {f ^ k i}) ≪≫ₗ
      piDropTrivial (fun i => F[X] ⧸ Ideal.span {f ^ k i}) (fun i => 0 < k i) (fun i hi => by
        have : k i = 0 := by omega
        rw [Ideal.Quotient.subsingleton_iff, this, pow_zero, Ideal.span_singleton_one]) ≪≫ₗ
      LinearEquiv.piCongrLeft' F[X] (fun i : {i : Fin d // 0 < k i} => F[X] ⧸ Ideal.span {f ^ k i}) σ
  refine ⟨_, fun i => k (σ.symm i), fun i => (σ.symm i).2, ⟨ψ⟩, fun j => ?_⟩
  haveI : ∀ e : ℕ, Module.Finite F (F[X] ⧸ Ideal.span {f ^ e}) := fun e =>
    (AdjoinRoot.powerBasis (pow_ne_zero e hf.ne_zero)).finite
  rw [(kerAevalEquivPi g _ ψ (f ^ j)).finrank_eq, Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => finrank_ker_lsmul_pow_quotient f hf.ne_zero _ j

end GlobalTheory.CuspGL
end
end

