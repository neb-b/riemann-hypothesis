module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CMTraceForms.ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth
section
private theorem idem_lt {R : Type} [CommRing R] {e x : R} (he : e * e = e)
    (hxe : x * e = x) (hne : x ≠ e) :
    Ideal.span ({1 - e} : Set R) < Ideal.span ({1 - x} : Set R) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨1 - e, by linear_combination (-1 : R) * hxe⟩
  · intro h
    have h1 : (1 - x) ∈ Ideal.span ({1 - e} : Set R) := by
      rw [h]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    apply hne
    linear_combination e * hc + c * he - hxe

private theorem idem_absorb {R : Type} [CommRing R] {s : ℕ} (g : Fin s → R)
    (h1 : ∀ i, g i * g i = g i) (h2 : ∀ i j, i ≠ j → g i * g j = 0) (i : Fin s) :
    g i * ∑ j, g j = g i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact h1 i
  · intro j _ hj
    exact h2 i j (Ne.symm hj)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem UpperTheory.exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (e : R), e * e = e →
      ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧
        (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e := by
  intro R _ _
  suffices H : ∀ I : Ideal R, ∀ e : R, Ideal.span ({1 - e} : Set R) = I → e * e = e →
      ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧
        (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e from fun e he => H _ e rfl he
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
  intro e hI he
  subst hI
  by_cases h0 : e = 0
  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp [h0]⟩
  by_cases hp : ∀ x : R, x * x = x → x * e = x → x = 0 ∨ x = e
  · refine ⟨1, fun _ => e, fun _ => ⟨he, h0, hp⟩, ?_, by simp⟩
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  push Not at hp
  obtain ⟨x, hx, hxe, hx0, hxne⟩ := hp
  have hy : (e - x) * (e - x) = e - x := by linear_combination he + hx - 2 * hxe
  have hye : (e - x) * e = e - x := by linear_combination he - hxe
  have hyne : e - x ≠ e := fun h => hx0 (by linear_combination -h)
  have hxy : x * (e - x) = 0 := by linear_combination hxe - hx
  obtain ⟨s, g, hg1, hg2, hg3⟩ := ih _ (idem_lt he hxe hxne) x rfl hx
  obtain ⟨t, k, hk1, hk2, hk3⟩ := ih _ (idem_lt he hye hyne) (e - x) rfl hy
  have hcross : ∀ i j, g i * k j = 0 := by
    intro i j
    have a := idem_absorb g (fun i => (hg1 i).1) hg2 i
    have b := idem_absorb k (fun i => (hk1 i).1) hk2 j
    rw [hg3] at a
    rw [hk3] at b
    calc g i * k j = (g i * x) * (k j * (e - x)) := by rw [a, b]
      _ = g i * k j * (x * (e - x)) := by ring
      _ = 0 := by rw [hxy, mul_zero]
  refine ⟨s + t, Fin.append g k, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using hg1 i
    | right i => simpa only [Fin.append_right] using hk1 i
  · intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        exact hg2 i j (fun h => hij (by rw [h]))
      | right j =>
        simp only [Fin.append_left, Fin.append_right]
        exact hcross i j
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left, Fin.append_right]
        rw [mul_comm]; exact hcross j i
      | right j =>
        simp only [Fin.append_right]
        exact hk2 i j (fun h => hij (by rw [h]))
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hg3, hk3]; ring
end

-- bundled from Development.AutomorphicArithmetic.CMTraceForms.ProdPrimeFactorsPowCeilPadicValNatMulEqPow
section
theorem UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow :
    ∀ (Q T a b : ℕ), Q ≠ 0 → ∏ p ∈ Q.primeFactors.filter Nat.Prime,
      p ^ (T * ⌈(padicValNat p Q : ℝ) * (a : ℝ)⌉.toNat + ⌈(padicValNat p Q : ℝ) * (b : ℝ)⌉.toNat) = Q ^ (T * a + b) := by
  intro Q T a b hQ
  have hc : ∀ m n : ℕ, ⌈(m : ℝ) * (n : ℝ)⌉.toNat = m * n := by
    intro m n
    rw [← Nat.cast_mul, Int.ceil_natCast, Int.toNat_natCast]
  have hf : Q.primeFactors.filter Nat.Prime = Q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  have hQ' : ∏ p ∈ Q.primeFactors, p ^ (Q.factorization p) = Q := by
    simpa only [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hQ
  rw [hf]
  conv_rhs => rw [← hQ', ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hc, hc, ← pow_mul, Nat.factorization_def Q (Nat.prime_of_mem_primeFactors hp),
    Nat.padicValNat_def]
  congr 1
  ring
end

-- bundled from Development.AutomorphicArithmetic.CMTraceForms.SumLogPrimeFactorsMulTwoAddLogbLe
section
theorem UpperTheory.sum_log_primeFactors_mul_two_add_logb_le :
    ∀ (Q : ℕ) (y : ℝ), Q ≠ 0 → 1 ≤ y → Real.log Q ≤ y →
      (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q) ≤ 11 * y ^ 4 := by
  intro Q y hQ hy hlog
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hpos : ∀ p ∈ Q.primeFactors, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have h1 : (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) ≤ y := by
    rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
    refine le_trans (Real.log_le_log (Finset.prod_pos hpos) ?_) hlog
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) (Nat.prod_primeFactors_dvd Q)
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr this
  have h2 : Real.logb 2 Q ≤ 2 * y := by
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) hQ1
  have h4 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy (by norm_num)
  calc (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q)
      ≤ y * (2 + Real.logb 2 Q) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ y * (4 * y) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ 11 * y ^ 4 := by nlinarith
end

