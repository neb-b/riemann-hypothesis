module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KapUnit
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

theorem kap_unit {K : Type} [NormedField K] [IsUltrametricDist K] (g2 g3 e : K) (h2 : ‖g2‖ ≤ 1)
    (h3 : ‖g3‖ ≤ 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (h22 : ‖(2 : K)‖ = 1)
    (he : 4 * e ^ 3 - g2 * e - g3 = 0) : ‖e‖ ≤ 1 ∧ ‖3 * e ^ 2 - g2 / 4‖ = 1 := by
  have hn1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have h4 : ‖(4 : K)‖ = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h22, one_mul]
  have h4ne : (4 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h4
    exact zero_ne_one h4
  have h3n : ‖(3 : K)‖ ≤ 1 := by simpa using hn1 3
  have h12n : ‖(12 : K)‖ ≤ 1 := by simpa using hn1 12
  have h15n : ‖(15 : K)‖ ≤ 1 := by simpa using hn1 15
  have h36n : ‖(36 : K)‖ ≤ 1 := by simpa using hn1 36
  have he1 : ‖e‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hE : 4 * e ^ 3 = g2 * e + g3 := by linear_combination he
    have hn : ‖(4 : K) * e ^ 3‖ = ‖e‖ ^ 3 := by rw [norm_mul, h4, one_mul, norm_pow]
    have hle : ‖g2 * e + g3‖ ≤ ‖e‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        nlinarith [norm_nonneg g2, norm_nonneg e]
      · linarith
    rw [← hE, hn] at hle
    have hsq : 1 < ‖e‖ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hsq (by linarith : (0 : ℝ) < ‖e‖)]
  refine ⟨he1, ?_⟩
  have hg3 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he
  have hid : g2 ^ 3 - 27 * g3 ^ 2 = (g2 - 12 * e ^ 2) * (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4) := by
    rw [hg3]
    ring
  have hk : 3 * e ^ 2 - g2 / 4 = -(g2 - 12 * e ^ 2) / 4 := by
    field_simp
    ring
  have hen : 0 ≤ ‖e‖ := norm_nonneg e
  have he2 : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ hen he1
  have he4 : ‖e‖ ^ 4 ≤ 1 := pow_le_one₀ hen he1
  have hQ : ‖g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) h2
      · rw [norm_neg, norm_mul, norm_mul, norm_pow]
        exact mul_le_one₀ (mul_le_one₀ h15n (by positivity) he2) (norm_nonneg _) h2
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ h36n (by positivity) he4
  have hP : ‖g2 - 12 * e ^ 2‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
    rw [norm_neg, norm_mul, norm_pow]
    exact mul_le_one₀ h12n (by positivity) he2
  have hP1 : 1 ≤ ‖g2 - 12 * e ^ 2‖ := by
    have := hΔ
    rw [hid, norm_mul] at this
    nlinarith [norm_nonneg (g2 - 12 * e ^ 2), norm_nonneg (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4)]
  rw [hk, norm_div, norm_neg, h4, div_one]
  exact le_antisymm hP hP1

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormEqOfNormSubLt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

open Polynomial Finset

variable (l : ℕ) [Fact l.Prime]

theorem norm_eq_of_norm_sub_lt' {a b : ℂ_[l]} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) h.ne
  rwa [sub_add_cancel, max_eq_right h.le] at this

theorem exists_root_near (P : ℂ_[l][X]) (hP : P.Monic) (x : ℂ_[l]) (h : ‖P.eval x‖ < 1) :
    ∃ a, P.IsRoot a ∧ ‖x - a‖ < 1 := by
  have hsplit : (P.roots.map fun a => X - C a).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP IsAlgClosed.card_roots_eq_natDegree
  by_contra hcon
  push Not at hcon
  have key : ∀ s : Multiset ℂ_[l], (∀ a ∈ s, 1 ≤ ‖x - a‖) →
      1 ≤ ‖((s.map fun a => X - C a).prod).eval x‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul]
      simp only [eval_sub, eval_X, eval_C]
      exact one_le_mul_of_one_le_of_one_le (hs a (Multiset.mem_cons_self _ _))
        (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))
  have := key P.roots (fun a ha => hcon a ((mem_roots hP.ne_zero).1 ha))
  rw [hsplit] at this
  linarith

theorem norm_pow_sub_one_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) : ‖y ^ k - 1‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hy, one_mul]
    exact ih

theorem norm_geom_sum_sub_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) :
    ‖(∑ i ∈ range k, y ^ i) - k‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (∑ i ∈ range (k + 1), y ^ i) - ((k + 1 : ℕ) : ℂ_[l]) =
        ((∑ i ∈ range k, y ^ i) - k) + (y ^ k - 1) := by
      rw [sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (norm_pow_sub_one_le l hy k))

theorem norm_geom_sum_eq_one {y : ℂ_[l]} (hy : ‖y - 1‖ < 1) {m : ℕ} (hm : ‖(m : ℂ_[l])‖ = 1) :
    ‖∑ i ∈ range m, y ^ i‖ = 1 := by
  have hy1 : ‖y‖ = 1 := by
    have := norm_eq_of_norm_sub_lt' l (a := y) (b := 1) (by rwa [norm_one])
    rwa [norm_one] at this
  have := norm_geom_sum_sub_le l hy1 m
  rw [← hm]
  exact norm_eq_of_norm_sub_lt' l (by rw [hm]; exact lt_of_le_of_lt this hy)

end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedPrime
section
namespace ReciprocityTheory.ChartRestriction.L1

open scoped NumberTheorySymbols

theorem prime_choice_class (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ a : ℕ, a % 3 = 2 ∧ J((a : ℤ) | d) = 1 := by
  obtain ⟨d', rfl⟩ := h3
  have hd'4 : d' % 4 = 1 := by omega
  have hd'1 : d' ≠ 1 := by
    rintro rfl
    exact hd3 rfl
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd'1
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hqd
    omega
  haveI := Fact.mk hq
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  obtain ⟨d'', rfl⟩ := hqd
  have hd''0 : d'' ≠ 0 := by
    rintro rfl
    simp at hd4
  haveI : NeZero d'' := ⟨hd''0⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hcop1 : Nat.Coprime q d'' := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).mpr ?_
    rintro ⟨e, rfl⟩
    exact absurd (Nat.isUnit_iff.mp (hsq q ⟨3 * e, by ring⟩)) hq.one_lt.ne'
  have hcop2 : Nat.Coprime 3 (q * d'') := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    rintro ⟨e, he⟩
    exact absurd (Nat.isUnit_iff.mp (hsq 3 ⟨e, by rw [he]; ring⟩)) (by norm_num)

  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop1 c.val 1
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcop2 2 b
  refine ⟨a, ?_, ?_⟩
  · unfold Nat.ModEq at ha1
    omega
  have hmq : a % q = c.val % q := (ha2.of_mul_right d'').trans hb1
  have hmd : a % d'' = 1 % d'' := (ha2.of_mul_left q).trans hb2
  have hm3 : a % 3 = 2 := by
    unfold Nat.ModEq at ha1
    omega
  have hJ3 : J((a : ℤ) | 3) = -1 := by
    rw [jacobiSym.mod_left]
    have : (a : ℤ) % ((3 : ℕ) : ℤ) = 2 := by omega
    rw [this]
    norm_num
  have hJq : J((a : ℤ) | q) = -1 := by
    have : (a : ℤ) % (q : ℤ) = (c.val : ℤ) % (q : ℤ) := by exact_mod_cast hmq
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, ← jacobiSym.legendreSym.to_jacobiSym,
      legendreSym.eq_neg_one_iff]
    simpa using hc
  have hJd : J((a : ℤ) | d'') = 1 := by
    have : (a : ℤ) % (d'' : ℤ) = ((1 : ℕ) : ℤ) % (d'' : ℤ) := by exact_mod_cast hmd
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, Nat.cast_one, jacobiSym.one_left]
  rw [jacobiSym.mul_right, jacobiSym.mul_right, hJ3, hJq, hJd]
  norm_num

theorem prime_choice_recip (d p : ℕ) (hd4 : d % 4 = 3) (hp : Odd p) :
    J(-(d : ℤ) | p) = J((p : ℤ) | d) := by
  have hd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hd]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd4 h]
    ring

theorem prime_choice_lift (d p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hd0 : 0 < d) (hdp : d < p)
    (hs : p ∣ s ^ 2 + d) : ∃ r : ℕ, Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨r0, hr0e, hr0⟩ : ∃ r0 : ℕ, Even r0 ∧ p ∣ r0 ^ 2 + d := by
    rcases Nat.even_or_odd s with he | ho
    · exact ⟨s, he, hs⟩
    · refine ⟨s + p, ho.add_odd hpodd, ?_⟩
      have e : (s + p) ^ 2 + d = (s ^ 2 + d) + p * (2 * s + p) := by ring
      rw [e]
      exact dvd_add hs (dvd_mul_right _ _)
  have hndvd : ¬ p ∣ r0 := by
    intro h
    have h2 : p ∣ r0 ^ 2 := dvd_pow h two_ne_zero
    have hpd : p ∣ d := (Nat.dvd_add_right h2).mp hr0
    have := Nat.le_of_dvd hd0 hpd
    omega
  by_cases hsq : p ^ 2 ∣ r0 ^ 2 + d
  ·
    refine ⟨r0 + 2 * p, hr0e.add (even_two_mul p), ?_, ?_⟩
    · have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p * (4 * r0 + 4 * p) := by ring
      rw [e]
      exact dvd_add hr0 (dvd_mul_right _ _)
    · intro h
      have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p ^ 2 * 4 + p * (4 * r0) := by ring
      rw [e] at h
      have h1 : p ^ 2 ∣ p * (4 * r0) := (Nat.dvd_add_right (dvd_add hsq (dvd_mul_right _ _))).mp h
      rw [pow_two] at h1
      have h2 : p ∣ 4 * r0 := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h4 | h4
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
      · exact hndvd h4
  · exact ⟨r0, hr0e, hr0, hsq⟩

theorem prime_choice (d b : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ p r : ℕ, p.Prime ∧ b < p ∧ d < p ∧ p % 3 = 2 ∧ Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  obtain ⟨a, ha3, ha⟩ := prime_choice_class d hsq hd4 h3 hd3
  have hd0 : d ≠ 0 := by omega
  haveI : NeZero d := ⟨hd0⟩
  have hunit : IsUnit (a : ZMod d) := by
    rw [ZMod.isUnit_iff_coprime]
    by_contra hnc
    have h0 : J((a : ℤ) | d) = 0 := jacobiSym.eq_zero_iff.mpr ⟨hd0, by simpa [Int.gcd_natCast_natCast] using hnc⟩
    rw [ha] at h0
    exact one_ne_zero h0
  obtain ⟨p, hpgt, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (b + d)
  have hpd : p % d = a % d := (ZMod.natCast_eq_natCast_iff' p a d).mp hpa
  have hp3 : p % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd p h3, hpd, Nat.mod_mod_of_dvd a h3, ha3]
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod : (p : ℤ) % (d : ℤ) = (a : ℤ) % (d : ℤ) := by exact_mod_cast hpd
  have hJ : J(-(d : ℤ) | p) = 1 := by
    rw [prime_choice_recip d p hd4 hpodd, jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, ha]
  haveI := Fact.mk hp
  have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (d : ZMod p) = 0 := by
      push_cast at h0
      simpa using h0
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff d p).mp h1)
    omega
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hne] at hJ
  obtain ⟨x, hx⟩ := hJ
  have hs : p ∣ x.val ^ 2 + d := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast at hx ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination -hx
  obtain ⟨r, hr1, hr2, hr3⟩ := prime_choice_lift d p x.val hp (by omega) (by omega) (by omega) hs
  exact ⟨p, r, hp, by omega, by omega, hp3, hr1, hr2, hr3⟩

end ReciprocityTheory.ChartRestriction.L1
end

