module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0009
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPos
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

lemma dhPos_iter_logMul (f : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih]
    ring

lemma dhPos_abscissa {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
  have h : abscissaOfAbsConv (↗ψ * ↗Λ) ≤ ((1 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ (by simp only [Complex.ofReal_re]; exact_mod_cast hy)
  exact lt_of_le_of_lt h (by exact_mod_cast hs)

lemma dhPos_iter {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    (-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s = LSeries (logMul^[k] (↗ψ * ↗Λ)) s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEq : ∀ z : ℂ, 1 < z.re → negLD ψ z = LSeries (↗ψ * ↗Λ) z := by
    intro z hz
    have hev : DirichletCharacter.LFunction ψ =ᶠ[nhds z] LSeries (fun n => ψ n) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    unfold negLD
    rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries ψ hz,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hz]
    ring
  have heq : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hEq z hz
  rw [heq.iteratedDeriv_eq, LSeries_iteratedDeriv k (dhPos_abscissa ψ hs), ← mul_assoc, ← mul_pow]
  norm_num

lemma dhPos_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ (term (logMul^[k] (↗ψ * ↗Λ)) s n).re)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s).re := by
  rw [dhPos_iter ψ k hs]
  have habs : abscissaOfAbsConv (logMul^[k] (↗ψ * ↗Λ)) < s.re := by
    have e : ∀ j : ℕ, abscissaOfAbsConv (logMul^[j] (↗ψ * ↗Λ)) = abscissaOfAbsConv (↗ψ * ↗Λ) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]
    rw [e]
    exact dhPos_abscissa ψ hs
  have hs2 := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  exact Complex.reCLM.hasSum hs2

lemma dhPos_term {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ u : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) ((σ : ℂ) + u * I) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * (ψ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    have hu : (n : ℂ) ^ ((u : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn')
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, Complex.cpow_add _ _ hn', hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

lemma dhPos_term_real {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) (σ : ℂ) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

lemma dhPos_term_nonneg {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    0 ≤ (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n).re
      + (term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [dhPos_term_real, dhPos_term_real, dhPos_term, dhPos_term]
  simp only [Complex.re_ofReal_mul]
  have hA0 : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have hz1 : ‖(n : ℂ) ^ ((γ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hw : -1 ≤ (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    have hnorm : ‖χ n / (n : ℂ) ^ ((γ : ℂ) * I)‖ ≤ 1 := by
      rw [norm_div, hz1, div_one]
      exact DirichletCharacter.norm_le_one χ _
    have h2 := Complex.abs_re_le_norm (χ n / (n : ℂ) ^ ((γ : ℂ) * I))
    linarith [(abs_le.1 h2).1]
  have key : 0 ≤ ((1 : DirichletCharacter ℂ q) n).re + (χ₁ n).re + (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re +
      ((χ * χ₁) n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    by_cases hu : IsUnit (n : ZMod q)
    · have h1n : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
      have hsq : χ₁ n * χ₁ n = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ q => ψ n) h1
        simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using e
      have hχ₁ : χ₁ n = 1 ∨ χ₁ n = -1 := by
        have h' : (χ₁ n - 1) * (χ₁ n + 1) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 h' with h | h
        · left
          linear_combination h
        · right
          linear_combination h
      rw [MulChar.mul_apply, h1n]
      rcases hχ₁ with h | h
      · rw [h, mul_one]
        simp only [Complex.one_re]
        linarith
      · rw [h]
        simp only [Complex.one_re, Complex.neg_re, mul_neg, mul_one, neg_div]
        linarith
    · have h0 : ∀ ψ : DirichletCharacter ℂ q, ψ n = 0 := fun ψ => MulChar.map_nonunit ψ hu
      simp [h0]
  nlinarith [mul_nonneg hA0 key]

theorem deuring_heilbronn_positivity : DHPos := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have H1 := dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs1
  have H2 := dhPos_hasSum χ₁ k hs1
  have H3 := dhPos_hasSum χ k hs2
  have H4 := dhPos_hasSum (χ * χ₁) k hs2
  have Hall := ((H1.add H2).add H3).add H4
  rw [mul_add, mul_add, mul_add, Complex.add_re, Complex.add_re, Complex.add_re]
  exact Hall.nonneg (fun n => dhPos_term_nonneg χ₁ χ h1 k σ γ n)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensDiv
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma divSq_harm (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  have h := harmonic_le_one_add_log x
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

lemma divSq_count (x : ℕ) : ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, if Nat.lcm p.1 p.2 ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    have hd : n.divisors = (Icc 1 x).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h, h0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hn.2⟩, h⟩
      · rintro ⟨_, h⟩
        exact ⟨h, by omega⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, sq, ← Nat.cast_mul,
      ← card_product, hd, ← filter_product]
    congr 2
    ext p
    simp [Nat.lcm_dvd_iff]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Nat.Ioc_filter_dvd_card_eq_div]
  rfl

lemma divSq_lcm {a b : ℕ} (ha : 1 ≤ a) :
    Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have h1 : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have h2 : Nat.gcd a b * (b / Nat.gcd a b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
    _ = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [h1, h2]
    _ = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by ring

lemma divSq_cube (x : ℕ) :
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ ≤ (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
    with hφ
  set F : ℕ × ℕ × ℕ → ℝ := fun t => ((t.1 : ℝ))⁻¹ * (((t.2.1 : ℝ))⁻¹ * ((t.2.2 : ℝ))⁻¹) with hF
  have hinj : Set.InjOn φ (Icc 1 x ×ˢ Icc 1 x : Finset (ℕ × ℕ)) := by
    intro p _ q _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨hg, h1, h2⟩ := h
    have e1 : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have e3 : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e4 : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    ext
    · calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) := e1.symm
        _ = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := by rw [h1, hg]
        _ = q.1 := e3
    · calc p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) := e2.symm
        _ = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := by rw [h2, hg]
        _ = q.2 := e4
  have hsub : (Icc 1 x ×ˢ Icc 1 x).image φ ⊆ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x) := by
    intro t ht
    rw [mem_image] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    simp only [mem_product, mem_Icc] at hp
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hp
    have hg : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ a1
    simp only [hφ, mem_product, mem_Icc]
    refine ⟨⟨hg, (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)) hg, (Nat.div_le_self _ _).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd b1 (Nat.gcd_dvd_right _ _)) hg, (Nat.div_le_self _ _).trans b2⟩⟩
  calc ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, F (φ p) := by
        refine sum_congr rfl fun p hp => ?_
        simp only [mem_product, mem_Icc] at hp
        rw [divSq_lcm hp.1.1]
        simp only [hF, hφ]
        push_cast
        rw [mul_inv, mul_inv, mul_assoc]
    _ = ∑ t ∈ (Icc 1 x ×ˢ Icc 1 x).image φ, F t := (sum_image hinj).symm
    _ ≤ ∑ t ∈ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x), F t := by
        refine sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => ?_
        simp only [hF]
        positivity
    _ = (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
        simp only [hF]
        rw [sum_product]
        simp only [sum_product, ← mul_sum, ← sum_mul]
        ring

theorem divisor_square_bound : DivSq := by
  intro x hx
  have hlog : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hH0 : 0 ≤ ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := sum_nonneg fun k _ => by positivity
  calc ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := divSq_count x
    _ ≤ ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, (x : ℝ) * ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by
        refine sum_le_sum fun p _ => ?_
        rw [← div_eq_mul_inv]
        exact Nat.cast_div_le
    _ = (x : ℝ) * ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ (x : ℝ) * (1 + Real.log x) ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg x)
        exact (divSq_cube x).trans (pow_le_pow_left₀ hH0 (divSq_harm x) 3)

theorem coefficient_block_bound : CoefficientBlockBound := by
  intro Y N U σ hU hσ
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := mco_norm_le Y N hn1
    have h2 : (n : ℝ) ^ (-σ) ≤ (U : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hU0 hUn (by linarith)
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h4 : ((U : ℝ) ^ (-σ)) ^ 2 = (U : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      congr 1
      push_cast
      ring
    calc (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
        ≤ ((n.divisors.card : ℝ) * (U : ℝ) ^ (-σ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) h3)
            (mul_le_mul h1 h2 h3 (Nat.cast_nonneg _)) 2
      _ = (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
          rw [mul_pow, h4, mul_comm]
  have hsub : Ioc U (2 * U) ⊆ Icc 1 (2 * U) := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  have hD := divisor_square_bound (2 * U) (by omega)
  have hpow : (U : ℝ) ^ (1 - 2 * σ) = (U : ℝ) ^ (-(2 * σ)) * U := by
    rw [show (1 - 2 * σ) = -(2 * σ) + 1 by ring, Real.rpow_add hU0, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Ioc U (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Icc 1 (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hU0.le _)
        exact sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * (((2 * U : ℕ) : ℝ) * (1 + Real.log ((2 * U : ℕ) : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hU0.le _)
    _ = 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
        rw [hpow]
        push_cast
        ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplEdge
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_left_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ T' B : ℝ) (hy : 1 ≤ y)
    (hσ : 1 / 2 ≤ σ₁) (hσ1 : σ₁ < 1) (hT' : 0 ≤ T')
    (hB : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ B) :
    ‖∫ t in (-T')..T', Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ 2 * T' * B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
  have hy0 : 0 < y := by linarith
  have hσp : 0 < σ₁ := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hT'))
  have hpt : ∀ t ∈ Set.uIoc (-T') T', ‖Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hBt := hB t (abs_le.mpr ⟨ht.1.le, ht.2⟩)
    set w : ℂ := (σ₁ : ℂ) + (t : ℂ) * I with hw
    have hre : w.re = σ₁ := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : σ₁ ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      rw [hre, abs_of_pos hσp] at this; exact this
    have hw2 : 1 - σ₁ ≤ ‖w - 1‖ := by
      have h1 : (w - 1).re = σ₁ - 1 := by simp [hre]
      have := Complex.abs_re_le_norm (w - 1)
      rw [h1, abs_of_neg (by linarith)] at this; linarith
    have hden : σ₁ * (1 - σ₁) ≤ ‖w‖ * ‖w - 1‖ :=
      mul_le_mul hw1 hw2 (by linarith) (norm_nonneg _)
    have hdp : 0 < σ₁ * (1 - σ₁) := mul_pos hσp (by linarith)
    have hyp : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ σ₁ / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₁ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) :=
          div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) hdp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  have : |T' - -T'| = 2 * T' := by rw [abs_of_nonneg (by linarith)]; ring
  rw [this]; ring

theorem ex_horiz_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ σ₀ v B : ℝ) (hy : 1 ≤ y)
    (hσ : σ₁ ≤ σ₀) (hv : 1 ≤ |v|) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ B) :
    ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤ (σ₀ - σ₁) * B * y ^ σ₀ / v ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hpt : ∀ x ∈ Set.uIoc σ₁ σ₀, ‖Fchi χ y ((x : ℂ) + v * I)‖ ≤ B * y ^ σ₀ / v ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hσ] at hx
    have hBx := hB x hx.1.le hx.2
    set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
    have hre : w.re = x := by simp [hw]
    have him : w.im = v := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : |v| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
    have hw2 : |v| ≤ ‖w - 1‖ := by
      have : (w - 1).im = v := by simp [him]
      rw [← this]; exact Complex.abs_im_le_norm _
    have hpow : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx.2
    have hden : v ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
      rw [← sq_abs]; nlinarith [abs_nonneg v]
    have htp : 0 < v ^ 2 := by rw [← sq_abs]; positivity
    have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ x / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₀ / v ^ 2 := div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) htp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith)]; ring

theorem ex_tail_half (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hf : ∀ t : ℝ, T < t → ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Set.Ioi T, f t‖ ≤ K / T := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have h := MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume.restrict (Set.Ioi T))
    (f := f) hint
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => by
      have ht0 : 0 < t := lt_trans hT ht
      have := hf t ht
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      simpa [div_eq_mul_inv] using this)))
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
  have : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

theorem ex_tail_gen (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T) (hi : MeasureTheory.Integrable f)
    (hf : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ K / t ^ 2) :
    ‖(∫ t : ℝ, f t) - ∫ t in (-T)..T, f t‖ ≤ 2 * K / T := by
  have h1 : (∫ t in Set.Iic (-T), f t) + ∫ t in Set.Ioi (-T), f t = ∫ t : ℝ, f t :=
    intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn
  have h2 : (∫ t in (-T)..T, f t) + ∫ t in Set.Ioi T, f t = ∫ t in Set.Ioi (-T), f t :=
    intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn
  have h3 : (∫ t in Set.Ioi T, f (-t)) = ∫ t in Set.Iic (-T), f t := integral_comp_neg_Ioi T f
  have e : (∫ t : ℝ, f t) - ∫ t in (-T)..T, f t
      = (∫ t in Set.Ioi T, f (-t)) + ∫ t in Set.Ioi T, f t := by
    rw [← h1, ← h2, h3]; ring
  rw [e]
  have a := ex_tail_half (fun t => f (-t)) K T hT (fun t ht => by
    have := hf (-t) (by rw [abs_neg]; exact lt_of_lt_of_le ht (le_abs_self t))
    simpa using this)
  have b := ex_tail_half f K T hT (fun t ht => hf t (lt_of_lt_of_le ht (le_abs_self t)))
  calc _ ≤ ‖∫ t in Set.Ioi T, f (-t)‖ + ‖∫ t in Set.Ioi T, f t‖ := norm_add_le _ _
    _ ≤ K / T + K / T := add_le_add a b
    _ = 2 * K / T := by ring

theorem ex_tail_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₀ T' : ℝ),
    1 ≤ y → 1 < σ₀ → 1 ≤ T' →
    ‖(∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + t * I)) - ∫ t in (-T')..T', Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * (1 / (σ₀ - 1) + C) * y ^ σ₀ / T' := by
  obtain ⟨C, hC, hR⟩ := l_log_deriv_right
  refine ⟨C, hC, ?_⟩
  intro M _ χ y σ₀ T' hy hσ hT'
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T' := by linarith
  obtain ⟨hint, -⟩ := perron_formula_character M χ y hy σ₀ hσ
  have h := ex_tail_gen (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) ((1 / (σ₀ - 1) + C) * y ^ σ₀) T' hT0 hint
    (fun t ht => by
      have ht0 : 0 < |t| := lt_trans hT0 ht
      show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
      set w : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hw
      have hre : w.re = σ₀ := by simp [hw]
      have him : w.im = t := by simp [hw]
      rw [norm_perron_integrand_eq χ y hy0 w, hre]
      have hζ : ‖negLD χ w‖ ≤ 1 / (σ₀ - 1) + C := by
        have := hR M χ w (by rw [hre]; exact hσ)
        rwa [hre] at this
      have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
      have hw2 : |t| ≤ ‖w - 1‖ := by
        have : (w - 1).im = t := by simp [him]
        rw [← this]; exact Complex.abs_im_le_norm _
      have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have htp : 0 < t ^ 2 := by rw [← sq_abs]; positivity
      have hnum : 0 ≤ 1 / (σ₀ - 1) + C := le_trans (norm_nonneg _) hζ
      have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
      calc ‖negLD χ w‖ * y ^ σ₀ / (‖w‖ * ‖w - 1‖)
          ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
        _ ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / t ^ 2 :=
            div_le_div_of_nonneg_left (mul_nonneg hnum hyp) htp hden)
  refine h.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

