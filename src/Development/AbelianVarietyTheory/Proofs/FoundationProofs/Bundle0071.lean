module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOne
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

section Character

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)

theorem exp_mem_range_of_isAlgClosed (x : ℚ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ Set.range ε := by
  have hMΩ : ((x.den : ℕ) : Ω) ≠ 0 := by
    intro h
    have := congrArg ε h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at this
    exact x.den_nz this
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨hMΩ⟩
  haveI : NeZero x.den := ⟨x.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← hx]; ring
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I _
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hw
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eOm_spec (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exp_mem_range_of_isAlgClosed ε x)

theorem eOm_add (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply ε.injective
  rw [map_mul, eOm_spec, eOm_spec, eOm_spec, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem eOm_zero : eOm ε 0 = 1 := by
  apply ε.injective
  rw [eOm_spec, map_one]; simp

end Character

section Coeff

variable {R : Type*} [CommRing R]

theorem cm_coeff (c : ℚ → R) (φ : HahnSeries ℚ R) (r : ℚ) : (cm c φ).coeff r = c r * φ.coeff r := rfl

theorem cm_mul (c : ℚ → R) (hc : ∀ r s, c (r + s) = c r * c s) (φ ψ : HahnSeries ℚ R) :
    cm c (φ * ψ) = cm c φ * cm c ψ := by
  ext r
  have h1 : (cm c φ).support ⊆ φ.support := fun t ht h => ht (by simp [cm_coeff, h])
  have h2 : (cm c ψ).support ⊆ ψ.support := fun t ht h => ht (by simp [cm_coeff, h])
  rw [cm_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, Finset.mul_sum]
  have e1 : ∀ ij ∈ Finset.antidiagonal φ.isPWO_support ψ.isPWO_support r,
      c r * (φ.coeff ij.1 * ψ.coeff ij.2) = (cm c φ).coeff ij.1 * (cm c ψ).coeff ij.2 := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    rw [cm_coeff, cm_coeff, ← hij.2.2, hc]; ring
  rw [Finset.sum_congr rfl e1]
  symm
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨h1 hij.1, h2 hij.2.1, hij.2.2⟩
  · intro ij hij hn
    rw [Finset.mem_antidiagonal] at hij hn
    by_contra hne
    exact hn ⟨(HahnSeries.mem_support _ _).2 (ne_zero_and_ne_zero_of_mul hne).1,
      (HahnSeries.mem_support _ _).2 (ne_zero_and_ne_zero_of_mul hne).2, hij.2.2⟩

theorem cm_one (c : ℚ → R) (hc : c 0 = 1) : cm c (1 : HahnSeries ℚ R) = 1 := by
  ext r
  rw [cm_coeff, HahnSeries.coeff_one]
  split_ifs with h
  · subst h; rw [hc, mul_one]
  · rw [mul_zero]

theorem scale_mul {a : ℚ} (ha : 0 < a) (φ ψ : HahnSeries ℚ R) : scale a (φ * ψ) = scale a φ * scale a ψ := by
  simp only [scale, dif_pos ha]
  exact HahnSeries.embDomain_mul _ (fun x y => by simp [mul_add]) φ ψ

theorem scale_one {a : ℚ} (ha : 0 < a) : scale a (1 : HahnSeries ℚ R) = 1 := by
  simp only [scale, dif_pos ha]
  exact HahnSeries.embDomain_one _ (by simp)

end Coeff

theorem sub_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d →
    ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  intro Ω _ _ _ ε a b d h φ ψ
  have hc : ∀ r s : ℚ, eOm ε ((r + s) * b / d) = eOm ε (r * b / d) * eOm ε (s * b / d) := by
    intro r s; rw [← eOm_add]; congr 1; ring
  have h0 : eOm ε (0 * b / d) = 1 := by rw [zero_mul, zero_div, eOm_zero]
  refine ⟨?_, ?_⟩
  · simp only [sub]; rw [cm_mul _ hc, scale_mul h]
  · simp only [sub]; rw [cm_one _ h0, scale_one h]

end GlobalTheory.CyclotomicQExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumLeProdOfTwoLeNat
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem sum_le_prod_of_two_le_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, 2 ≤ f i) : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have key : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i ∧ 2 ≤ ∏ i ∈ s, f i := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using h a (by simp)
    | cons a s ha hs ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_cons_of_mem hi))
      have h3 := h a (Finset.mem_cons_self _ _)
      constructor
      · have := Nat.add_le_mul h3 h2
        omega
      · nlinarith
  exact key.1

private theorem arith_four (a b c R m : ℕ) (ha : 16 ≤ a) (hb : m ≤ b) (hc : m ≤ c)
    (hbc : 16 * m ≤ b * c) (hR : 1 ≤ R) : 4 * m * (a + b + c + R) ≤ a * b * c * R := by
  have h1 : 16 * m * a ≤ b * c * a := Nat.mul_le_mul_right _ hbc
  have h2 : 16 * m * b ≤ a * c * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hc)
  have h3 : 16 * m * c ≤ a * b * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hb)
  have h4 : 16 * m * R ≤ a * b * c * R := by
    apply Nat.mul_le_mul_right
    calc 16 * m ≤ b * c := hbc
      _ ≤ a * (b * c) := Nat.le_mul_of_pos_left _ (by omega)
      _ = a * b * c := by ring
  have h5 : a * b * c ≤ a * b * c * R := Nat.le_mul_of_pos_right _ hR
  nlinarith

theorem sum_primePowerParts_le :
    ∀ n q d : ℕ, 0 < n → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → 16 ≤ max q d →
      16 * q * d ∣ n → (∑ l ∈ n.primeFactors, ((l ^ padicValNat l n : ℕ) : ℝ)) ≤
        (n : ℝ) / (4 * ((min q d : ℕ) : ℝ)) := by
  intro n q d hn hq hd hq2 hd2 hqd hmax hdvd
  set f : ℕ → ℕ := fun l => l ^ padicValNat l n with hf
  have hpow : ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ f p := by
    intro p k hp hk
    haveI := Fact.mk hp
    exact Nat.pow_le_pow_right hp.pos (((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn.ne').1 hk)
  have hge : ∀ p ∈ n.primeFactors, p ≤ f p := by
    intro p hp
    have := hpow p 1 (Nat.prime_of_mem_primeFactors hp)
      (by simpa using Nat.dvd_of_mem_primeFactors hp)
    simpa using this
  have h16 : 2 ^ 4 ∣ n := Dvd.dvd.trans ⟨q * d, by ring⟩ hdvd
  have hqn : q ∣ n := Dvd.dvd.trans ⟨16 * d, by ring⟩ hdvd
  have hdn : d ∣ n := Dvd.dvd.trans ⟨16 * q, by ring⟩ hdvd
  have m2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, Dvd.dvd.trans ⟨8, by norm_num⟩ h16, hn.ne'⟩
  have mq : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
  have md : d ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdn, hn.ne'⟩
  have ha : 16 ≤ f 2 := by simpa using hpow 2 4 Nat.prime_two h16
  have hb := hge q mq
  have hc := hge d md
  have hsub : ({2, q, d} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hn2 : (2 : ℕ) ∉ ({q, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hprod : ∏ l ∈ n.primeFactors, f l = n := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
    simp [f, Nat.padicValNat_def]
  set s := n.primeFactors \ {2, q, d} with hs
  have hs2 : ∀ i ∈ s, 2 ≤ f i := fun i hi =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hi).1).two_le.trans
      (hge i (Finset.mem_sdiff.1 hi).1)
  have hSP := sum_le_prod_of_two_le_nat s f hs2
  have hR : 1 ≤ ∏ i ∈ s, f i :=
    Finset.prod_pos (f := f) fun i hi => lt_of_lt_of_le (by norm_num) (hs2 i hi)
  have e1 : n = f 2 * f q * f d * ∏ i ∈ s, f i := by
    rw [← hprod, ← Finset.prod_sdiff hsub, Finset.prod_insert hn2, Finset.prod_pair hqd]
    ring
  have e2 : ∑ l ∈ n.primeFactors, f l = f 2 + f q + f d + ∑ i ∈ s, f i := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_insert hn2, Finset.sum_pair hqd]
    ring
  have hbc : 16 * min q d ≤ f q * f d := by
    calc 16 * min q d ≤ max q d * min q d := Nat.mul_le_mul_right _ hmax
      _ = q * d := max_mul_min q d
      _ ≤ f q * f d := Nat.mul_le_mul hb hc
  have key := arith_four (f 2) (f q) (f d) (∏ i ∈ s, f i) (min q d) ha
    ((min_le_left _ _).trans hb) ((min_le_right _ _).trans hc) hbc hR
  rw [← e1] at key
  have key2 : (∑ l ∈ n.primeFactors, f l) * (4 * min q d) ≤ n := by
    rw [e2, mul_comm]
    exact (Nat.mul_le_mul_left _ (by omega)).trans key
  have hm : 0 < min q d := lt_min hq.pos hd.pos
  rw [le_div_iff₀ (by positivity), ← Nat.cast_sum]
  exact_mod_cast key2

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPrimePowerPartPowSubOneLe
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem sum_le_prod_of_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha2 := h a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · simp
    · have hne : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => by
        have := h i (Finset.mem_insert_of_mem hi)
        omega
      have hP : 2 ≤ ∏ i ∈ s, f i :=
        (h b (Finset.mem_insert_of_mem hb)).trans
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Finset.dvd_prod_of_mem f hb))
      nlinarith

private theorem prod_prime_pow_dvd_of_forall_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ)
    (hp : ∀ l ∈ s, l.Prime) (hd : ∀ l ∈ s, l ^ e l ∣ M) : ∏ l ∈ s, l ^ e l ∣ M := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd a (Finset.mem_insert_self a s))
      (ih (fun l hl => hp l (Finset.mem_insert_of_mem hl)) (fun l hl => hd l (Finset.mem_insert_of_mem hl)))
    refine Nat.Coprime.prod_right fun l hl => ?_
    refine Nat.Coprime.pow _ _ ?_
    exact (Nat.coprime_primes (hp a (Finset.mem_insert_self a s)) (hp l (Finset.mem_insert_of_mem hl))).mpr
      (by rintro rfl; exact ha hl)

theorem sum_prime_pow_le_of_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ) (hM : M ≠ 0)
    (hp : ∀ l ∈ s, l.Prime) (he : ∀ l ∈ s, e l ≠ 0) (hd : ∀ l ∈ s, l ^ e l ∣ M) :
    ∑ l ∈ s, l ^ e l ≤ M := by
  have h2 : ∀ l ∈ s, 2 ≤ l ^ e l := fun l hl => le_trans (hp l hl).two_le (Nat.le_self_pow (he l hl) l)
  exact (sum_le_prod_of_two_le s _ h2).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (prod_prime_pow_dvd_of_forall_dvd s e M hp hd))

private theorem padicValNat_pow_sub_one_eq_add (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) :
    padicValNat l (g ^ d - 1) = padicValNat l (g - 1) + padicValNat l d := by
  rw [Nat.padicValNat_def, Nat.padicValNat_def, Nat.padicValNat_def]
  have := Fact.mk hl
  have hlg' : ¬ l ∣ g := by
    intro h
    have h' := Nat.dvd_sub h hlg
    have e : g - (g - 1) = 1 := by omega
    rw [e] at h'
    exact hl.one_lt.ne' (Nat.dvd_one.mp h')
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hx : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg'
    have h4' : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have := Int.natCast_dvd_natCast.mpr h4
      rwa [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one, Nat.cast_ofNat] at this
    have key := Int.two_pow_sub_pow' d h4' hx
    rw [one_pow] at key
    have e1 : (g : ℤ) ^ d - 1 = ((g ^ d - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
      push_cast
      ring
    have e2 : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ g)]
      push_cast
      ring
    have e3 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have hN : g ^ d - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))
    rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hN,
      padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0), padicValNat_eq_emultiplicity hd]
    exact key
  · have := padicValNat.pow_sub_pow hodd (by omega : 1 < g) hlg hlg' hd
    rwa [one_pow] at this

theorem pow_padicValNat_pow_sub_one_dvd (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) : l ^ padicValNat l (g ^ d - 1) ∣ d * (g - 1) := by
  rw [padicValNat_pow_sub_one_eq_add g d l hg h4 hd hl hlg, pow_add, mul_comm d]
  exact mul_dvd_mul (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))

theorem sum_primePowerPart_pow_sub_one_le :
    ∀ g d : ℕ, 2 ≤ g → 4 ∣ g - 1 → 2 ≤ d → (∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ≤ d * ((g : ℝ) - 1) + ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
  intro g d hg h4 hd
  set N := g ^ d - 1 with hN
  have hd0 : d ≠ 0 := by omega
  have hg1 : g - 1 ≠ 0 := by omega
  have hdiv : g - 1 ∣ N := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  have hv : ∀ l ∈ N.primeFactors, padicValNat l N ≠ 0 := by
    intro l hl
    obtain ⟨hlp, hlN, hN0⟩ := Nat.mem_primeFactors.mp hl
    have := Fact.mk hlp
    rw [Nat.padicValNat_def]
    exact Nat.one_le_iff_ne_zero.mp (one_le_multiplicity_of_dvd hN0 hlN)
  have hnat : ∑ l ∈ N.primeFactors, l ^ padicValNat l N ≤ d * (g - 1) + N / (g - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (fun l => l ∣ g - 1)]
    refine add_le_add ?_ ?_
    · refine sum_prime_pow_le_of_dvd _ _ _ (mul_ne_zero hd0 hg1)
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      exact pow_padicValNat_pow_sub_one_dvd g d l hg h4 hd0 (Nat.mem_primeFactors.mp hl1).1 hlg
    · have hQ0 : N / (g - 1) ≠ 0 := by
        intro h0
        have hm := Nat.div_mul_cancel hdiv
        rw [h0, zero_mul] at hm
        have : 1 < g ^ d := Nat.one_lt_pow hd0 (by omega)
        omega
      refine sum_prime_pow_le_of_dvd _ _ _ hQ0
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      obtain ⟨hlp, -, -⟩ := Nat.mem_primeFactors.mp hl1
      have hcop : Nat.Coprime (l ^ padicValNat l N) (g - 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hlg)
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [Nat.div_mul_cancel hdiv]
      exact (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hcast_g1 : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ g)]
    simp
  have hcast_N : ((N : ℕ) : ℝ) = (g : ℝ) ^ d - 1 := by
    rw [hN, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    simp
  have hcast_Q : ((N / (g - 1) : ℕ) : ℝ) = ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
    rw [Nat.cast_div hdiv (by rw [hcast_g1]; linarith), hcast_N, hcast_g1]
  calc (∑ l ∈ N.primeFactors, ((l ^ padicValNat l N : ℕ) : ℝ))
        = ((∑ l ∈ N.primeFactors, l ^ padicValNat l N : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ((d * (g - 1) + N / (g - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = _ := by rw [Nat.cast_add, Nat.cast_mul, hcast_g1, hcast_Q]

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumUnitsPrimePowTeichmullerReindex
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem sum_units_primePow_teichmuller_reindex :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (m : ℕ) (A : Type) [AddCommMonoid A] (f : ZMod (p ^ (m + 1)) → A),
      ∑ b : (ZMod (p ^ (m + 1)))ˣ, f (b : ZMod (p ^ (m + 1))) =
        ∑ c : (ZMod p)ˣ, ∑ l ∈ Finset.range (p ^ m),
          f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1))) := by
  intro p hp hp2 m A _ f
  have hpp : p.Prime := hp.out
  haveI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hcop : ∀ (c : (ZMod p)ˣ) (l : ℕ),
      Nat.Coprime ((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l) (p ^ (m + 1)) := by
    intro c l
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.mul_left
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h0 : (((c : ZMod p).val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [ZMod.natCast_zmod_val] at h0
      exact c.ne_zero h0
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).1 (by rwa [add_comm] at h)
      exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)
  let g : (ZMod p)ˣ × Fin (p ^ m) → (ZMod (p ^ (m + 1)))ˣ :=
    fun x => ZMod.unitOfCoprime _ (hcop x.1 x.2)
  have hg : ∀ x, (g x : ZMod (p ^ (m + 1))) =
      (((x.1 : ZMod p).val ^ (p ^ m) * (1 + p) ^ (x.2 : ℕ) : ℕ) : ZMod (p ^ (m + 1))) := fun x => rfl
  have hinj : Function.Injective g := by
    rintro ⟨c, l⟩ ⟨c', l'⟩ h
    have h' := congrArg (fun u : (ZMod (p ^ (m + 1)))ˣ => (u : ZMod (p ^ (m + 1)))) h
    simp only [hg] at h'
    have hc : c = c' := by
      have h2 := congrArg (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero m)) (ZMod p)) h'
      simp only [map_natCast] at h2
      push_cast at h2
      simp only [ZMod.natCast_val, ZMod.cast_id', id, ZMod.natCast_self, add_zero, one_pow, mul_one,
        ZMod.pow_card_pow] at h2
      exact Units.ext h2
    subst hc
    have hu : IsUnit ((((c : ZMod p).val ^ (p ^ m) : ℕ) : ZMod (p ^ (m + 1)))) :=
      (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) (hcop c 0))
    have h3 : ((1 + p : ZMod (p ^ (m + 1)))) ^ (l : ℕ) = (1 + p) ^ (l' : ℕ) := by
      rw [Nat.cast_mul, Nat.cast_mul] at h'
      have h4 := hu.mul_left_cancel h'
      push_cast at h4
      exact h4
    have hu1 : IsUnit ((1 + p : ℕ) : ZMod (p ^ (m + 1))) := by
      refine (ZMod.isUnit_iff_coprime _ _).2 ?_
      have h5 := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) (hcop c 1)
      rwa [pow_one] at h5
    obtain ⟨u, hu⟩ := hu1
    push_cast at hu
    have h6 : u ^ (l : ℕ) = u ^ (l' : ℕ) := Units.ext (by push_cast [hu]; exact h3)
    rw [pow_inj_mod, ← orderOf_units, hu, ZMod.orderOf_one_add_prime hpp hp2, Nat.mod_eq_of_lt l.2,
      Nat.mod_eq_of_lt l'.2] at h6
    exact Prod.ext rfl (Fin.ext h6)
  have hcard : Fintype.card ((ZMod p)ˣ × Fin (p ^ m)) = Fintype.card (ZMod (p ^ (m + 1)))ˣ := by
    rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Fintype.card_fin,
      Nat.totient_prime_pow_succ hpp, Nat.totient_prime hpp]
    ring
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩
  rw [← Fintype.sum_bijective g hbij (fun x => f (g x : ZMod (p ^ (m + 1)))) (fun b => f b)
    (fun _ => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Fin.sum_univ_eq_sum_range
    (fun l => f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1)))) (p ^ m)

end GlobalTheory
end

