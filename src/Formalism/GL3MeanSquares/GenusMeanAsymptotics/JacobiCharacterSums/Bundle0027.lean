module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0024
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0014

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplNeg
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

lemma ex_sum_le {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)

lemma ex_one_le_log {M : ℕ} (hM : 3 ≤ M) (t : ℝ) : 1 ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h0 := abs_nonneg t
  have h6 : (6 : ℝ) ≤ (M : ℝ) * (|t| + 2) := by nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem ex_negLD_bound : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ) (δ : ℝ),
    3 ≤ M → 0 < δ → δ ≤ 1 / 20 → 19 / 20 ≤ s.re → s.re ≤ 3 → s ≠ 1 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → ‖ρ - s‖ ≤ 1 / 5 → δ ≤ ‖ρ - s‖) →
    ‖negLD χ s‖ ≤ C * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  obtain ⟨C₁, hC₁, hloc⟩ := ex_local
  refine ⟨2 * C₁ + (100 / 7 + C₀), by positivity, ?_⟩
  intro M _ χ s δ hM hδ hδ' hs1 _ hsne hz
  set large₂ : ℝ := Real.log ((M : ℝ) * (|s.im| + 2)) with hLg
  have hL1 : 1 ≤ large₂ := ex_one_le_log hM s.im
  have hif : (0 : ℝ) ≤ (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
    split_ifs
    · positivity
    · exact le_rfl

  have hup : ∀ x : ℝ, 0 ≤ x → x ≤ x * large₂ / δ := by
    intro x hx
    rw [le_div_iff₀ hδ]
    have : x * δ ≤ x * 1 := mul_le_mul_of_nonneg_left (by linarith) hx
    have h2 : x * 1 ≤ x * large₂ := mul_le_mul_of_nonneg_left hL1 hx
    linarith
  by_cases hcase : 107 / 100 ≤ s.re
  · have h1 := hR M χ s (by linarith)
    have h2 : 1 / (s.re - 1) ≤ 100 / 7 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 := hup (2 * C₁ + (100 / 7 + C₀)) (by positivity)
    linarith
  · rw [not_le] at hcase
    obtain ⟨Z, hZ, hcard, hexp⟩ := hloc M χ s.im hM
    have hne : exLF χ s ≠ 0 := by
      intro h0
      have := hz s h0 (by linarith) (by simp)
      simp at this
      linarith
    have hsb : s ∈ Metric.closedBall ((101 / 100 : ℂ) + s.im * I) (1 / 15) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : s - ((101 / 100 : ℂ) + s.im * I) = ((s.re - 101 / 100 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hE := hexp s hsb hne
    have hdist : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
      intro ρ hρ
      obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
      rw [norm_sub_rev]
      by_cases h9 : 9 / 10 ≤ ρ.re
      · refine hz ρ hρ0 h9 ?_
        rw [Metric.mem_closedBall] at hρb hsb
        have := dist_triangle_right ρ s ((101 / 100 : ℂ) + s.im * I)
        rw [dist_eq_norm] at this
        linarith
      · rw [not_le] at h9
        have := Complex.abs_re_le_norm (ρ - s)
        rw [Complex.sub_re] at this
        have h3 := neg_abs_le (ρ.re - s.re)
        linarith
    have hS := ex_sum_le hδ Z (exOrd χ) s hdist
    have hS2 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) / δ ≤ C₁ * large₂ / δ :=
      div_le_div_of_nonneg_right hcard hδ.le
    have hD : ‖deriv (exLF χ) s / exLF χ s‖ ≤ C₁ * large₂ + C₁ * large₂ / δ := by
      have := norm_sub_norm_le (deriv (exLF χ) s / exLF χ s) (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ))
      linarith
    have hCL : C₁ * large₂ ≤ C₁ * large₂ / δ := by
      rw [le_div_iff₀ hδ]
      have : 0 ≤ C₁ * large₂ := by positivity
      nlinarith
    have hI : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ = (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
      split_ifs <;> simp
    rw [negLD_eq_exLF χ hsne hne]
    have hN := norm_sub_le (if χ = 1 then 1 / (s - 1) else 0 : ℂ) (deriv (exLF χ) s / exLF χ s)
    rw [hI] at hN
    have hex : (2 * C₁ + (100 / 7 + C₀)) * large₂ / δ = 2 * (C₁ * large₂ / δ) + (100 / 7 + C₀) * large₂ / δ := by ring
    have hpos : 0 ≤ (100 / 7 + C₀) * large₂ / δ := by positivity
    rw [hex]
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PrimeCountOfPsi
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem prime_count_of_psi : PiOf := by
  rintro ⟨c, A, C₀, hc, hP⟩
  obtain ⟨c₁, hc₁, hηl⟩ := etaOf_lower 1 one_pos
  refine ⟨min (c / 2) (c ^ 2 / 2), 10 * |A| + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁,
    max (2 * C₀) 16, lt_min (by positivity) (by positivity), ?_⟩
  intro M _ h8
  refine ⟨eOf M, fun p hp => eOf_exc M p hp, fun h χ₁ β₁ => eOf_none M h χ₁ β₁, ?_⟩
  intro X b hX2 hrange hb
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8n : 8 ≤ M := Nat.le_of_dvd hMpos h8
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast hM8n
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hll : 1 ≤ Real.log (Real.log M + 2) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ Real.log M + 2)
    linarith
  have hprod : Real.log M ≤ Real.log M * Real.log (Real.log M + 2) := by nlinarith
  have hprod0 : 0 ≤ Real.log M * Real.log (Real.log M + 2) := by linarith
  have hrange' : max (2 * C₀) 16 * (Real.log M * Real.log (Real.log M + 2)) ≤ Real.log X := by
    rw [← mul_assoc]; exact hrange
  have hL16 : 16 * Real.log M ≤ Real.log X := by
    have := mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) 16) hprod0
    linarith
  have hLC : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X / 2 := by
    have := mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) 16) hprod0
    have e : C₀ * Real.log M * Real.log (Real.log M + 2) =
        2 * C₀ * (Real.log M * Real.log (Real.log M + 2)) / 2 := by ring
    rw [e]
    linarith
  have hX0 : 0 < X := by linarith
  have hX4 : 4 ≤ X := by
    rw [← Real.log_le_log_iff (by norm_num) hX0]
    linarith
  have hs2 : 2 ≤ √X := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have hη0 : 0 ≤ etaOf M := (etaOf_pos M (by omega)).le
  have hη1 := etaOf_le_one M
  have hηl' := hηl M (by omega)
  have hP' : ∀ y : ℝ, √X ≤ y → y ≤ X →
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      |A| * y * etaOf M *
        (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y)))) := by
    intro y h1 h2
    have hy2 : 2 ≤ y := hs2.trans h1
    have hly : Real.log X / 2 ≤ Real.log y := by
      rw [← Real.log_sqrt hX0.le]
      exact Real.log_le_log (by linarith) h1
    refine (hP M h8 y hy2 (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)) hη0) (by positivity)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [he] at hP'
    have e0 : mainAP (none : Option (DirichletCharacter ℂ M × ℝ)) b X =
        (liX X - 0 * liX (X ^ (1 : ℝ))) / (M.totient : ℝ) := by simp [mainAP]
    rw [e0]
    exact pi_core M h8 b hb none (by simp) (by norm_num) le_rfl
      (fun t _ => mainPsi_sum_none M b hb t 1) hη0 hη1 (Or.inl le_rfl) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'
  · rw [he] at hP'
    obtain ⟨_, _, _, hβlo, hβ1⟩ := eOf_exc M _ he
    have hχ := eOf_char_sq M χ₁ β₁ he b ((ZMod.isUnit_iff_coprime b M).mpr hb)
    have hθ : |(χ₁ (b : ZMod M)).re| ≤ 1 := by rcases hχ with h | h <;> simp [h]
    have hβ : 1 / 2 ≤ β₁ := by
      have : 1 / (8 * Real.log M) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      simp only [] at hβlo
      linarith
    have hηe := etaOf_some M χ₁ β₁ he
    have e1 : mainAP (some (χ₁, β₁)) b X =
        (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ) := rfl
    rw [e1]
    exact pi_core M h8 b hb (some (χ₁, β₁)) hθ hβ hβ1.le
      (fun t ht => mainPsi_sum_some M b hb χ₁ β₁ t ht hχ) hη0 hη1
      (Or.inr (by rw [hηe]; exact min_le_right _ _)) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.SecondBlockCount
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem second_block_count (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)) (U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 256 ≤ qd M T)
    (hc : 971882496 * Real.log (qd M T) ^ 5 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) U (fun n => p.1 (n : ZMod M)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (256 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le_second (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le_second (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log q := dyadic_index_le_log_second q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) := by
    have : 0 < pJd M T := by unfold pJd; omega
    exact_mod_cast this
  have hl0 : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
  have hl : 1 + Real.log (2 * (U : ℝ)) ≤ 13 * Real.log q := by
    have h1 : (2 * (U : ℝ)) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU2
    have h2 : Real.log (2 * (U : ℝ)) ≤ Real.log ((q : ℝ) ^ 12) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hG : 9 + 8 * Real.log (2 * T + 1) ≤ 17 * Real.log x := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    linarith
  have hG0 : 0 ≤ 9 + 8 * Real.log (2 * T + 1) := by
    have : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    linarith
  have hK0 : 0 ≤ 8 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * q := by
    have : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * x := by rw [hx]; nlinarith
    linarith
  have hθ : (0 : ℝ) < 1 / (2 * (pJd M T : ℝ)) := by positivity
  have hsmall := second_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * ((M : ℝ) + 1) * (2 + 2 * T)) (pJd M T : ℝ) q (Real.sqrt q) (Real.log q) (by linarith)
    (Real.sqrt_pos.2 (by linarith)) (rpow_neg_exponent_bound_second q U σ (by omega) hσ hU1) (by linarith) hl hK0 hK
    hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod M)) (fun p => p.2) (pYd M T) (pNd M T) U σ
    (1 / (2 * (pJd M T : ℝ))) (9 + 8 * Real.log (2 * T + 1)) (8 * ((M : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound M S σ T U hU hT (by linarith) hS hsp) hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound_second q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (1 / (2 * (pJd M T : ℝ))) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * (4 * (pJd M T : ℝ) ^ 2) := by
    field_simp
    ring
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  gcongr

theorem zero_count_second : Count1 := by
  obtain ⟨q₁, hq₁⟩ := log_pow_five_le_sqrt 971882496
  refine ⟨48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)), max q₁ 256, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq256 : 256 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_max_left _ _) hq)
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le_second (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let Sj : ℕ → Finset (DirichletCharacter ℂ M × ℂ) := fun j =>
    S.filter (fun p => 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => p.1 (n : ZMod M)) p.2‖)
  have hsub : S ⊆ (range (pJd M T)).biUnion Sj := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    obtain ⟨j, hj, hjb⟩ := zero_detection_second M p.1 h1 T hT hM p.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ B := by
    intro j hj
    have hjJ : j < pJd M T := mem_range.1 hj
    have hYN : qd M T ^ 3 * 2 ^ pJd M T ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve_second (qd M T) hq256
    apply second_block_count M T σ (Sj j) (pYd M T * 2 ^ j) hM hT hσ hσ1 hq256 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ j) = qd M T ^ 3 * 2 ^ (j + 1) := by unfold pYd; ring
        _ ≤ qd M T ^ 3 * 2 ^ pJd M T := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨-, h2, h3, h4, -⟩ := hS p (mem_filter.1 hp).1
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp'
      exact hsp p (mem_filter.1 hp).1 p' (mem_filter.1 hp').1
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ (pJd M T : ℝ) * B := by
    have := sum_le_card_nsmul (range (pJd M T)) (fun j => ((Sj j).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log (qd M T) := dyadic_index_le_log_second (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (256 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq256
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : (pJd M T : ℝ) * B ≤ 48 * Real.log ((M : ℝ) * T) * B := by gcongr
  have h4 : 48 * Real.log ((M : ℝ) * T) * B =
      48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 7 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 7 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

