module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def DHTuran2 : Prop :=
  ∃ (C : ℝ) (A : ℕ), 0 < C ∧ 1 ≤ A ∧ ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n →
    (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + A * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (A * n) ≤ ‖∑ i, z i ^ k‖

def DHDom : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (γ σ : ℝ) (k : ℕ), χ₁ ^ 2 = 1 → 1 < σ →
    ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I) + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ ≤
      ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re

def DHIneqF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T η : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    19 / 20 ≤ β₁ → β₁ < 1 → IsLZero χ ρ → 22 / 25 ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    0 < η → η ≤ 2 / 25 →
    ∃ (N : ℕ) (w : Fin N → ℂ),
      (∀ i, η ≤ (w i).re) ∧
      (∃ i, w i = ((η + (1 - ρ.re) : ℝ) : ℂ)) ∧
      (∑ i, 1 / w i).re ≤ 2 * (1 - β₁) / η ^ 2 + C * Real.log ((M : ℝ) * T) * 25 ∧
      ∀ j : ℕ, 1 ≤ j →
        ‖∑ i, 1 / (w i) ^ j‖ ≤
          ((-1 : ℂ) ^ (j - 1) * (iteratedDeriv (j - 1) (negLD (1 : DirichletCharacter ℂ M)) ((1 + η : ℝ) : ℂ)
              + iteratedDeriv (j - 1) (negLD χ₁) ((1 + η : ℝ) : ℂ))).re / ((j - 1).factorial : ℝ)
          + 2 * j * (1 - β₁) / η ^ (j + 1) + C * Real.log ((M : ℝ) * T) * 25 ^ j

def DHHyper : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (y x : ℝ), 3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
    1 ≤ y → y ≤ x →
    ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
      ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y) + C * M * (Real.log y + 1) / Real.sqrt y

def DHPrime : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ σ : ℝ) (k : ℕ),
    3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 → 1 < σ → σ ≤ 2 →
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1))

def DHIneqFOf : Prop := DHPos → DHLocal → DHDom → DHIneqF

def DHPrimeOf : Prop := DHHyper → DHPrime

def DHFinish2Of : Prop := DHTuran2 → DHIneqF → DHPrime → DeuringHeilbronnMB

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DyadicSizeLePowTwelveSecond
section
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem log_pow_five_le_sqrt (c : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 5 ≤ Real.sqrt q := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 10)).bound
    (c := 1 / (c ^ 2 + 1)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨⌈x₀⌉₊, fun q hq => ?_⟩
  have hqx : x₀ ≤ (q : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hq)
  have h1 := hx₀ q hqx
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hq0] at h1
  have h2 : Real.log q ^ 10 ≤ 1 / (c ^ 2 + 1) * q := (le_abs_self _).trans h1
  have h3 : (c ^ 2 + 1) * Real.log q ^ 10 ≤ q := by
    have hp : (0 : ℝ) < c ^ 2 + 1 := by positivity
    calc (c ^ 2 + 1) * Real.log q ^ 10 ≤ (c ^ 2 + 1) * (1 / (c ^ 2 + 1) * q) := by gcongr
      _ = (q : ℝ) := by field_simp
  have h4 : (c * Real.log q ^ 5) ^ 2 ≤ q := by
    have : (0 : ℝ) ≤ Real.log q ^ 10 := by positivity
    nlinarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h4)

theorem one_le_log_of_three_le_second {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem dyadic_index_le_log_second (q : ℕ) (hq : 3 ≤ q) : ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) ≤ 24 * Real.log q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 q ≤ q := by exact_mod_cast h1
  have h3 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have h4 := Real.log_two_gt_d9
  have h5 := one_le_log_of_three_le_second hq'
  have h6 : (0 : ℝ) ≤ (Nat.log 2 q : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem dyadic_size_le_pow_twelve_second (q : ℕ) (hq : 256 ≤ q) : q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1)) ≤ q ^ 12 := by
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ (8 * (Nat.log 2 q + 1)) = 256 * (2 ^ Nat.log 2 q) ^ 8 := by
    rw [← pow_mul]; rw [show 8 * (Nat.log 2 q + 1) = 8 + Nat.log 2 q * 8 by ring, pow_add]; norm_num
  rw [h2]
  calc q ^ 3 * (256 * (2 ^ Nat.log 2 q) ^ 8) ≤ q ^ 3 * (q * q ^ 8) := by gcongr
    _ = q ^ 12 := by ring

theorem second_small_condition (u l K J q s Lq : ℝ) (hq : 0 < q) (hs : 0 < s) (hu : u ≤ 1 / (q * s))
    (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 48 * q) (hJ0 : 0 < J) (hJ : J ≤ 24 * Lq)
    (hc : 971882496 * Lq ^ 5 ≤ s) : 2 * u * l ^ 3 * K ≤ (1 / (2 * J)) ^ 2 / 2 := by
  have hL : 0 < Lq := by nlinarith
  have h1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by
    have : 0 ≤ 1 / (q * s) := by positivity
    calc 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by gcongr
      _ ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by gcongr
  have h2 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) = 210912 * Lq ^ 3 / s := by
    field_simp; ring
  have h3 : 1 / (4608 * Lq ^ 2) ≤ (1 / (2 * J)) ^ 2 / 2 := by
    have : (1 / (2 * J)) ^ 2 / 2 = 1 / (8 * J ^ 2) := by field_simp; ring
    rw [this]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h4 : 210912 * Lq ^ 3 / s ≤ 1 / (4608 * Lq ^ 2) := by
    rw [div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

theorem rpow_neg_exponent_bound_second (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

theorem rpow_pos_exponent_bound_second (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have hU' : (U : ℝ) ≤ (2 * x) ^ 12 := by
    calc (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
      _ ≤ (2 * x) ^ 12 := by gcongr
  have h1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hU' (by linarith)
  have h2 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 * x) ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have h3 : (2 * x) ^ (24 * (1 - σ)) = 2 ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) :=
    Real.mul_rpow (by norm_num) hx.le
  have h4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    have : (2 : ℝ) ^ (6 : ℝ) = 64 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h5 : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  rw [h2, h3] at h1
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.OneLeLogOfThreeLe
section
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem log_pow_seven_le_sqrt (c : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 7 ≤ Real.sqrt q := by
  have h := isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hb := h.bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  have hn := tendsto_natCast_atTop_atTop.eventually hb
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp (hn.and (Filter.eventually_ge_atTop 1))
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hq₀ q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h2
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h1
  have e7 : Real.log q ^ (7 : ℝ) = Real.log q ^ 7 := by
    exact_mod_cast Real.rpow_natCast (Real.log q) 7
  rw [e7, ← Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  calc c * Real.log q ^ 7 ≤ |c| * Real.log q ^ 7 :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (1 / (|c| + 1) * Real.sqrt q) := by gcongr
    _ ≤ Real.sqrt q := by
        rw [← mul_assoc]
        apply mul_le_of_le_one_left hs
        rw [mul_one_div, div_le_one (by positivity)]
        linarith

theorem one_le_log_of_three_le' {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem dyadic_index_le_log (q : ℕ) (hq : 3 ≤ q) :
    ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h1 : ((2 : ℝ) ^ Nat.log 2 q) ≤ q := by exact_mod_cast hpow
  have h2 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have hl2 := Real.log_two_gt_d9
  have hlq : 1 ≤ Real.log q := one_le_log_of_three_le' (by exact_mod_cast hq)
  have hn0 : (0 : ℝ) ≤ Nat.log 2 q := Nat.cast_nonneg _
  have h3 : 0.6931471803 * (Nat.log 2 q : ℝ) ≤ Real.log q := by nlinarith
  push_cast
  linarith

theorem dyadic_size_le_pow_twelve (q : ℕ) (hq : 512 ≤ q) :
    2 * (q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1))) ≤ q ^ 12 := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  generalize Nat.log 2 q = n at hpow ⊢
  have h8 : 2 ^ (8 * (n + 1)) = 256 * (2 ^ n) ^ 8 := by
    rw [show 8 * (n + 1) = n * 8 + 8 by ring, pow_add, pow_mul]
    ring
  have h9 : (2 ^ n) ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hpow 8
  rw [h8]
  calc 2 * (q ^ 3 * (256 * (2 ^ n) ^ 8)) ≤ 2 * (q ^ 3 * (256 * q ^ 8)) := by gcongr
    _ = 512 * q ^ 11 := by ring
    _ ≤ q * q ^ 11 := by gcongr
    _ = q ^ 12 := by ring

theorem first_small_condition (u l K J q s Lq c : ℝ) (hq : 0 < q) (hs : 0 < s) (hc0 : 0 < c)
    (hu : u ≤ 1 / (q * s)) (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 16 * q)
    (hJ0 : 0 < J) (hJ : J ≤ 25 * Lq) (hc : 87880000 / c ^ 2 * Lq ^ 7 ≤ s) :
    2 * u * l ^ 3 * K ≤ (c / (J * Lq)) ^ 2 / 2 := by
  have hL : 0 < Lq := by linarith
  have hlK : 0 ≤ l ^ 3 * K := by positivity
  have step1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by
    have := mul_le_mul_of_nonneg_right hu hlK
    nlinarith
  have step2 : 2 * (1 / (q * s)) * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) := by
    gcongr
  have step3 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) = 70304 * Lq ^ 3 / s := by
    field_simp
    ring
  have hJL : (c / (25 * Lq * Lq)) ^ 2 / 2 ≤ (c / (J * Lq)) ^ 2 / 2 := by
    gcongr
  have hc' : 87880000 * Lq ^ 7 ≤ s * c ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hc
    exact hc
  have step4 : 70304 * Lq ^ 3 / s ≤ (c / (25 * Lq * Lq)) ^ 2 / 2 := by
    have e : (c / (25 * Lq * Lq)) ^ 2 / 2 = c ^ 2 / (1250 * Lq ^ 4) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

theorem rpow_neg_exponent_bound (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

theorem rpow_pos_exponent_bound (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have he : 0 ≤ 2 - 2 * σ := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hUq : (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
  have s1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((q : ℝ) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hUq he
  have s2 : ((q : ℝ) ^ 12) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) := by
    apply Real.rpow_le_rpow (by positivity) _ he
    gcongr
  have s3 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx.le]
    rw [show ((12 : ℕ) : ℝ) * (2 - 2 * σ) = 24 * (1 - σ) by push_cast; ring]
  have s4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    calc (2 : ℝ) ^ (24 * (1 - σ)) ≤ (2 : ℝ) ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  have hx' : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  calc (U : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
        rw [← s3]; exact s1.trans s2
    _ ≤ 64 * x ^ (24 * (1 - σ)) := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsmB
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def excI {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) : ℝ :=
  match e with
  | none => 0
  | some (χ₁, _) => if χ = χ₁ then 1 else 0

def excT {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  match e with
  | none => 0
  | some (χ₁, β₁) => if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0

theorem mainPsi_eq {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) :
    mainPsi e χ y = (if χ = 1 then (y : ℂ) else 0) - excT e χ y := rfl

theorem sum_excI_le {M : ℕ} [NeZero M] (e : Option (DirichletCharacter ℂ M × ℝ)) :
    ∑ χ : DirichletCharacter ℂ M, excI e χ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excI]
  · have h : (∑ χ : DirichletCharacter ℂ M, excI (some (χ₁, β₁)) χ) = excI (some (χ₁, β₁)) χ₁ :=
      Finset.sum_eq_single χ₁ (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ _) h)
    rw [h]
    exact (if_pos rfl).le

theorem excW_le_one {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) :
    excW e χ ρ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW]
  · simp only [excW]; split_ifs <;> norm_num

theorem card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  exact_mod_cast Nat.totient_le M

theorem sum_excW_le {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y : ℝ) (hy : 1 ≤ y) (hZ : ∀ ρ ∈ Z, ρ.re < 1) :
    ∑ ρ ∈ Z, (excW e χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ excI e χ := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI]
  · simp only [excW, excI]
    by_cases h : χ = χ₁
    · simp only [h, true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℝ)) * y ^ (ρ.re - 1)
          = if ρ = (β₁ : ℂ) then y ^ (ρ.re - 1) else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs with hm
      · exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [hZ _ hm])
      · norm_num
    · simp [h]

theorem excT_sub_le {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y κ T : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) :
    ‖excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI, excT]
  · obtain ⟨-, hne, hz, hlo, hhi⟩ := he _ rfl
    simp only at hne hz hlo hhi
    simp only [excW, excI, excT]
    by_cases h : χ = χ₁
    · subst h
      simp only [true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℂ)) * (y : ℂ) ^ ρ / ρ
          = if ρ = (β₁ : ℂ) then (y : ℂ) ^ ρ / ρ else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      have hy0 : 0 < y := by linarith
      split_ifs with hm
      · simp only [sub_self, norm_zero, one_mul]; positivity
      · have hb : β₁ < 1 - κ / 2 := by
          by_contra hcon
          push Not at hcon
          exact hm (hZ _ ⟨Or.inl hne, hz⟩ (by simpa using hcon) (by simpa using hT))
        have hl : 1 ≤ Real.log M := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          have : (3 : ℝ) ≤ M := by exact_mod_cast hM
          linarith [Real.exp_one_lt_d9]
        have hb2 : 1 / 2 ≤ β₁ := by
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num); linarith
          linarith
        rw [sub_zero, one_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have h1 : y ^ β₁ ≤ y ^ (1 - κ / 2) := Real.rpow_le_rpow_of_exponent_le hy hb.le
        have h2 : y ^ (1 - κ / 2) = y * y ^ (-(κ / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_one]
        rw [div_le_iff₀ (by linarith)]
        have h3 : 0 ≤ y * y ^ (-(κ / 2)) := by positivity
        nlinarith
    · simp [h]

theorem one_char {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (m : ℂ → ℕ) (y κ T R : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z)
    (hre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re) (hm : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hR : ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ R) :
    ‖psiChi χ y - mainPsi e χ y‖ ≤
      R + 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1)
        + excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have e1 : psiChi χ y - mainPsi e χ y
      = (psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ)
        - ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        + (excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ) := by
    rw [mainPsi_eq]
    have : ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        = ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [this]
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]; ring
    · simp only [if_neg hχ]; ring
  have h2 : ‖∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ‖
      ≤ 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro ρ hρ
    have hw : (0 : ℝ) ≤ (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : ((excW e χ ρ : ℕ) : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast (excW_le_one e χ ρ).trans (hm ρ hρ)
      linarith
    have hn : ‖(m ρ : ℂ) - (excW e χ ρ : ℂ)‖ = (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : (m ρ : ℂ) - (excW e χ ρ : ℂ) = (((m ρ : ℝ) - (excW e χ ρ : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg hw]
    have hρn : 1 / 2 ≤ ‖ρ‖ := (hre ρ hρ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm ρ))
    rw [norm_div, norm_mul, hn, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have h3 : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
      rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
    rw [div_le_iff₀ (by linarith), h3]
    have h4 : 0 ≤ ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * (y * y ^ (ρ.re - 1)) := by positivity
    nlinarith
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hR h2)) ?_)
  exact excT_sub_le hM e he χ Z y κ T hy hT hZ

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

