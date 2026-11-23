module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle0001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0006

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDefs
section
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

abbrev PC := Σ N : ℕ, DirichletCharacter ℂ (N + 1)

def cv (p : PC) (n : ℕ) : ℂ := p.2 (n : ZMod (p.1 + 1))

def s0 : ℝ := 1 - 1 / 400

def mco (Y N n : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n), (((μ p.1 : ℤ)) : ℂ)

def blk (Y N U : ℕ) (p : PC) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc U (2 * U), mco Y N n * cv p n * (n : ℂ) ^ (-s)

def DualIneq : Prop :=
  ∀ (ι κ : Type) (S : Finset ι) (I : Finset κ) (b : κ → ℂ) (v : ι → κ → ℂ) (Δ : ℝ), 0 ≤ Δ →
    (∀ i ∈ S, ∑ j ∈ S, ‖∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ) →
    ∑ i ∈ S, ‖∑ n ∈ I, b n * v i n‖ ^ 2 ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * Δ

def PairSum : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ M : ℕ,
    ‖∑ n ∈ range M, cv p n * (starRingEnd ℂ) (cv p' n)‖ ≤ (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ)

def PairTwist : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ w : ℂ, 0 < w.re → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w)‖ ≤
      2 * (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖)

def MollId : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (Y N K : ℕ), 1 ≤ Y → Y ≤ N → Y * N ≤ K →
    (∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) *
        (∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)) =
      1 + ∑ n ∈ Ioc Y K, mco Y N n * χ (n : ZMod q) * (n : ℂ) ^ (-s)

def CoeffSq : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Y N U : ℕ, 1 ≤ U →
    ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))

def q0 (Q : ℝ) : ℕ := ⌈Q⌉₊
def pY (Q : ℝ) : ℕ := q0 Q ^ 4
def pJ (Q : ℝ) : ℕ := 8 * (Nat.log 2 (q0 Q) + 1)
def pN (Q : ℝ) : ℕ := 2 ^ pJ Q

def Detect : Prop :=
  ∀ (Q : ℝ), 20 ≤ Q → ∀ p : PC, p.2.IsPrimitive → p.1 ≠ 0 → ((p.1 + 1 : ℕ) : ℝ) ≤ Q →
    ∀ ρ : ℂ, s0 < ρ.re → |ρ.im| ≤ Q → DirichletCharacter.LFunction p.2 ρ = 0 →
      ∃ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p ρ‖

def BlockCount : Prop :=
  ∀ C : ℝ, 0 ≤ C → (∀ Y N U : ℕ, 1 ≤ U →
      ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))) →
  ∀ (Q : ℝ), 3 ≤ Q → ∀ (Y N U J : ℕ), 1 ≤ U → 1 ≤ J →
    8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) ≤ 1 / (8 * (J : ℝ) ^ 2) →
    ∀ (T : Finset PC) (ρ : PC → ℂ),
      (∀ p ∈ T, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ s0 < (ρ p).re ∧ (ρ p).re < 1 ∧
        |(ρ p).im| ≤ Q ∧ 1 / (2 * (J : ℝ)) ≤ ‖blk Y N U p (ρ p)‖) →
      (T.card : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ)

def Num : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ Q₀ C' : ℝ, 20 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
    (∀ j ∈ range (pJ Q), 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤
      1 / (8 * (pJ Q : ℝ) ^ 2)) ∧
    1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) ≤ C' * Q ^ (1 / 4 : ℝ)

def PairTwistOf : Prop := PairSum → PairTwist
def CoeffSqOf : Prop := Formalism.FX.DivisorBound → CoeffSq
def DetectOf : Prop := MollId → Detect
def BlockCountOf : Prop := DualIneq → PairTwist → BlockCount
def FinalOf : Prop := CoeffSq → Detect → BlockCount → Num → ZeroDensityBox

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqJac
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem soutPart_pos (m₀ N : ℕ) : 0 < soutPart m₀ N := by
  unfold soutPart
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem soutPart_squarefree (m₀ N : ℕ) : Squarefree (soutPart m₀ N) := by
  unfold soutPart
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_) fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)).mpr hpr

theorem soutPart_coprime (m₀ N : ℕ) : (soutPart m₀ N).Coprime m₀ := by
  unfold soutPart
  exact Nat.Coprime.prod_left fun p hp =>
    (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).mpr
      (Finset.mem_filter.mp hp).2.2

theorem soutPart_odd (m₀ N : ℕ) (h2 : 2 ∣ m₀) : Odd (soutPart m₀ N) := by
  exact Nat.coprime_two_right.mp ((soutPart_coprime m₀ N).coprime_dvd_right h2)

theorem soutPart_dvd (m₀ N : ℕ) : soutPart m₀ N ∣ N := by
  unfold soutPart
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd N)

theorem soutPart_le (m₀ N : ℕ) (hN : 0 < N) : soutPart m₀ N ≤ N := by
  exact Nat.le_of_dvd hN (soutPart_dvd m₀ N)

theorem jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ) :
    jacobiSym (∏ i ∈ s, f i) b = ∏ i ∈ s, jacobiSym (f i) b := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, jacobiSym.mul_left, ih]

theorem jacobiSym_prod_right {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
    rw [Finset.prod_cons, Finset.prod_cons,
      jacobiSym.mul_right' _ (hf a (Finset.mem_cons.mpr (Or.inl rfl))) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

theorem recip_sign_congr (p q q' : ℕ) (h4 : q % 4 = q' % 4) :
    ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ (p / 2 * (q' / 2)) := by
  have h : (q / 2) % 2 = (q' / 2) % 2 := by omega
  calc ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ ((p / 2 * (q / 2)) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1) ^ ((p / 2 * (q' / 2)) % 2) := by rw [Nat.mul_mod, h, ← Nat.mul_mod]
    _ = (-1) ^ (p / 2 * (q' / 2)) := (neg_one_pow_eq_pow_mod_two _).symm

theorem gcd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℤ).gcd (q : ℤ) = 1) ∧ ((q : ℤ).gcd (p : ℤ) = 1) := by
  have h := (Nat.coprime_primes hp hq).mpr hpq.ne
  refine ⟨?_, ?_⟩
  · rw [Int.gcd_natCast_natCast]
    exact h
  · rw [Int.gcd_natCast_natCast]
    exact h.symm

theorem jacobi_prime_in {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : p ∣ m₀) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q = jacobiSym (p : ℤ) q' := by
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  rcases hp.eq_two_or_odd' with rfl | hpo
  · have h8m : q % 8 = q' % 8 := Nat.ModEq.of_dvd h8 hqq
    have hz : (q : ZMod 8) = (q' : ZMod 8) := (ZMod.natCast_eq_natCast_iff' q q' 8).mpr h8m
    simp only [Nat.cast_ofNat]
    rw [jacobiSym.at_two hqo, jacobiSym.at_two hq'o, hz]
  · have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
    have hpm' : q % p = q' % p := Nat.ModEq.of_dvd hpm hqq
    rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o,
      recip_sign_congr p q q' h4, jacobiSym.mod_left (q : ℤ), jacobiSym.mod_left (q' : ℤ),
      ← Int.natCast_mod, ← Int.natCast_mod, hpm']

theorem jacobi_prime_out {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : ¬ p ∣ m₀) (hq : q.Prime)
    (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q * jacobiSym (q : ℤ) p = jacobiSym (p : ℤ) q' * jacobiSym (q' : ℤ) p := by
  have hp2 : p ≠ 2 := fun h => hpm (h ▸ dvd_trans (by norm_num) h8)
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hpo := hp.odd_of_ne_two hp2
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
  have s1 : jacobiSym (q : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq hpq).2
  have s2 : jacobiSym (q' : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq' hpq').2
  rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o, mul_assoc, mul_assoc,
    ← sq, ← sq, s1, s2, recip_sign_congr p q q' h4]

theorem jacobi_class_prod (m₀ N q : ℕ) (hN : 0 < N) :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      ∏ p ∈ N.primeFactors, (jacobiSym (p : ℤ) q ^ (N.factorization p) *
        (if Odd (N.factorization p) ∧ ¬ p ∣ m₀ then jacobiSym (q : ℤ) p else 1)) := by
  have hNfac : (N : ℤ) = ∏ p ∈ N.primeFactors, (p : ℤ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN.ne']
    rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
    simp only [Nat.cast_pow]
  rw [hNfac, jacobiSym_prod_left]
  unfold soutPart
  rw [jacobiSym_prod_right _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero,
    Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [jacobiSym.pow_left]

theorem jacobi_class_congr {m₀ N q q' : ℕ} (h8 : 8 ∣ m₀) (hN : 0 < N) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hNq : N < q) (hNq' : N < q') :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      jacobiSym (N : ℤ) q' * jacobiSym (q' : ℤ) (soutPart m₀ N) := by
  rw [jacobi_class_prod m₀ N q hN, jacobi_class_prod m₀ N q' hN]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpN : p ≤ N := Nat.le_of_mem_primeFactors hp
  have hpq : p < q := by omega
  have hpq' : p < q' := by omega
  by_cases hpm : p ∣ m₀
  · rw [if_neg (fun h => h.2 hpm), if_neg (fun h => h.2 hpm), mul_one, mul_one,
      jacobi_prime_in h8 hpP hpm hq hq' hqq hpq hpq']
  · have hsq : ∀ r : ℕ, r.Prime → p < r → jacobiSym (p : ℤ) r ^ 2 = 1 := fun r hr hpr =>
      jacobiSym.sq_one (gcd_prime_lt hpP hr hpr).1
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (N.factorization p)
    · have hnodd : ¬ Odd (N.factorization p) := Nat.not_odd_iff_even.mpr ⟨k, by omega⟩
      rw [if_neg (fun h => hnodd h.1), if_neg (fun h => hnodd h.1), mul_one, mul_one, hk, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow]
    · have hodd : Odd (N.factorization p) := ⟨k, hk⟩
      rw [if_pos ⟨hodd, hpm⟩, if_pos ⟨hodd, hpm⟩, hk, pow_succ, pow_succ, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow, one_mul, one_mul]
      exact jacobi_prime_out h8 hpP hpm hq hq' hqq hpq hpq'

theorem jacobi_class (m₀ a₀ N : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hN : 0 < N) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ q : ℕ, q.Prime → q % m₀ = a₀ % m₀ → N < q →
      jacobiSym (N : ℤ) q = σ * jacobiSym (q : ℤ) (soutPart m₀ N) := by
  have hcop1 : ∀ q : ℕ, q.Prime → N < q → (N : ℤ).gcd q = 1 := by
    intro q hq hNq
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => absurd (Nat.le_of_dvd hN h) (by omega)).symm
  have hcop2 : ∀ q : ℕ, q.Prime → N < q → (q : ℤ).gcd (soutPart m₀ N) = 1 := by
    intro q hq hNq
    have hle := soutPart_le m₀ N hN
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
      absurd (Nat.le_of_dvd (soutPart_pos m₀ N) h) (by omega)
  by_cases hex : ∃ q₀ : ℕ, q₀.Prime ∧ q₀ % m₀ = a₀ % m₀ ∧ N < q₀
  · obtain ⟨q₀, hq₀, hq₀m, hNq₀⟩ := hex
    refine ⟨jacobiSym (N : ℤ) q₀ * jacobiSym (q₀ : ℤ) (soutPart m₀ N), ?_, fun q hq hqm hNq => ?_⟩
    · rcases jacobiSym.eq_one_or_neg_one (hcop1 q₀ hq₀ hNq₀) with h | h <;>
        rcases jacobiSym.eq_one_or_neg_one (hcop2 q₀ hq₀ hNq₀) with h' | h' <;> simp [h, h']
    · have hc := jacobi_class_congr h8 hN hq hq₀ (hqm.trans hq₀m.symm) hNq hNq₀
      have hsq : jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 = 1 := jacobiSym.sq_one (hcop2 q hq hNq)
      rw [← hc]
      calc jacobiSym (N : ℤ) q = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 := by
            rw [hsq, mul_one]
        _ = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) * jacobiSym (q : ℤ) (soutPart m₀ N) := by
            ring
  · exact ⟨1, Or.inl rfl, fun q hq hqm hNq => absurd ⟨q, hq, hqm, hNq⟩ hex⟩

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqOrth
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem jacobi_congr {a b s : ℕ} (h : a ≡ b [MOD s]) : jacobiSym (a : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [jacobiSym.mod_left (a : ℤ), jacobiSym.mod_left (b : ℤ)]
  have h' : a % s = b % s := h
  rw [← Int.natCast_mod, ← Int.natCast_mod, h']

theorem exists_jacobi_neg_one (m t : ℕ) (ht : Odd t) (hsq : Squarefree t) (h1 : 1 < t)
    (hc : t.Coprime m) : ∃ u : ℕ, u ≡ 1 [MOD m] ∧ jacobiSym (u : ℤ) t = -1 := by
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
  haveI := Fact.mk hp
  obtain ⟨t', rfl⟩ := hpt
  have ht0 : t' ≠ 0 := by
    rintro rfl
    simp at h1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr ht) (even_two_mul t')
  have hpt' : ¬ p ∣ t' := by
    rintro ⟨k, rfl⟩
    have := hsq p ⟨k, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hcp : p.Coprime t' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpt'
  have hpm : p.Coprime m := Nat.Coprime.coprime_dvd_left (Dvd.intro t' rfl) hc
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.mul_right hcp hpm) a.val 1
  refine ⟨k, Nat.ModEq.of_mul_left t' hk2, ?_⟩
  haveI : NeZero t' := ⟨ht0⟩
  rw [jacobiSym.mul_right, jacobi_congr hk1, jacobi_congr (Nat.ModEq.of_mul_right m hk2),
    ← jacobiSym.legendreSym.to_jacobiSym p, (legendreSym.eq_neg_one_iff p).mpr (by simpa using ha)]
  simp

private theorem dvd_of_jacobiSym_agree_on_residue_class (m₀ s₁ s₂ : ℕ) (h1 : Odd s₁) (h2 : Odd s₂)
    (hq1 : Squarefree s₁) (hc1 : s₁.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ ∣ s₂ := by
  by_contra hnd
  have hs1 : s₁ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h1) ⟨0, rfl⟩
  have hs2 : s₂ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h2) ⟨0, rfl⟩
  have hgd : Nat.gcd s₁ s₂ ∣ s₁ := Nat.gcd_dvd_left s₁ s₂
  have hg0 : Nat.gcd s₁ s₂ ≠ 0 := Nat.gcd_ne_zero_left hs1
  have hga : Nat.gcd s₁ s₂ * (s₁ / Nat.gcd s₁ s₂) = s₁ := Nat.mul_div_cancel' hgd
  have hgb : Nat.gcd s₁ s₂ * (s₂ / Nat.gcd s₁ s₂) = s₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right s₁ s₂)
  set g := Nat.gcd s₁ s₂ with hg
  set a := s₁ / g with ha
  set b := s₂ / g with hb
  have ha0 : a ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hga
    exact hs1 hga.symm
  have ha1 : a ≠ 1 := by
    rintro h0
    rw [h0, mul_one] at hga
    exact hnd (hga ▸ Nat.gcd_dvd_right s₁ s₂)
  have hadv : a ∣ s₁ := Dvd.intro_left g hga
  have hao : Odd a := Odd.of_dvd_nat h1 hadv
  have haq : Squarefree a := Squarefree.squarefree_of_dvd hadv hq1
  have hag : a.Coprime g := by
    have := hq1
    rw [← hga] at this
    exact (Nat.squarefree_mul_iff.mp this).1.symm
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero hg0)
  have has2 : a.Coprime s₂ := by
    rw [← hgb]
    exact Nat.Coprime.mul_right hag hab
  have ham : a.Coprime m₀ := Nat.Coprime.coprime_dvd_left hadv hc1
  obtain ⟨u, hu1, hJ⟩ := exists_jacobi_neg_one (m₀ * s₂) a hao haq
    (lt_of_le_of_ne (Nat.pos_of_ne_zero ha0) (Ne.symm ha1))
    (Nat.Coprime.mul_right ham has2)
  have hum : u ≡ 1 [MOD m₀] := Nat.ModEq.of_mul_right s₂ hu1
  have hus : u ≡ 1 [MOD s₂] := Nat.ModEq.of_mul_left m₀ hu1
  have hug : u ≡ 1 [MOD g] := Nat.ModEq.of_dvd (Nat.gcd_dvd_right s₁ s₂) hus
  haveI : NeZero g := ⟨hg0⟩
  haveI : NeZero a := ⟨ha0⟩
  have hJs : jacobiSym (u : ℤ) s₂ = 1 := by
    rw [jacobi_congr hus]
    simp
  have hJg : jacobiSym (u : ℤ) g = 1 := by
    rw [jacobi_congr hug]
    simp
  have hJ1 : jacobiSym (u : ℤ) s₁ = -1 := by
    rw [← hga, jacobiSym.mul_right, hJg, hJ]
    ring
  have hua : u.Coprime a := by
    by_contra hn
    have h0 : jacobiSym (u : ℤ) a = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hn
    rw [h0] at hJ
    norm_num at hJ
  have hus' : u.Coprime s₂ := by
    have e : Nat.gcd u s₂ = Nat.gcd 1 s₂ := Nat.ModEq.gcd_eq hus
    rw [Nat.gcd_one_left] at e
    exact e
  have hug' : u.Coprime g := Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right s₁ s₂) hus'
  have hus1 : u.Coprime s₁ := by
    rw [← hga]
    exact Nat.Coprime.mul_right hug' hua
  have := h u hum (Nat.Coprime.mul_right hus1 hus')
  rw [hJ1, hJs] at this
  norm_num at this

theorem jacobi_separate (m₀ s₁ s₂ : ℕ) (hm : 0 < m₀) (h1 : Odd s₁) (h2 : Odd s₂) (hq1 : Squarefree s₁)
    (hq2 : Squarefree s₂) (hc1 : s₁.Coprime m₀) (hc2 : s₂.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ = s₂ := by
  apply Nat.dvd_antisymm
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₁ s₂ h1 h2 hq1 hc1 h
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₂ s₁ h2 h1 hq2 hc2
      (fun u hu hc => (h u hu (by rwa [mul_comm])).symm)

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

private lemma intervalIntegrable_inv_log_two {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 Y := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact Set.mem_compl_singleton_iff.2 (by linarith [ht.1] : (0 : ℝ) < t).ne'
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact (Real.log_pos (by linarith [ht.1])).ne'

theorem liX_upper {Y : ℝ} (hY : 2 ≤ Y) : 0 ≤ liX Y ∧ liX Y ≤ 2 * Y := by
  have hpos : ∀ t ∈ Set.Icc (2 : ℝ) Y, 0 < Real.log t := fun t ht => Real.log_pos (by linarith [ht.1])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  constructor
  · unfold liX
    exact intervalIntegral.integral_nonneg hY (fun t ht => (one_div_pos.2 (hpos t ht)).le)
  · unfold liX
    calc ∫ t in (2 : ℝ)..Y, 1 / Real.log t ≤ ∫ t in (2 : ℝ)..Y, (2 : ℝ) := by
          apply intervalIntegral.integral_mono_on hY (intervalIntegrable_inv_log_two hY) intervalIntegrable_const
          intro t ht
          have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
          rw [div_le_iff₀ (hpos t ht)]
          linarith
      _ = (Y - 2) * 2 := by simp
      _ ≤ 2 * Y := by linarith

theorem liX_lower {X : ℝ} (hX : 4 ≤ X) : X / (2 * Real.log X) ≤ liX X := by
  have hX2 : (2 : ℝ) ≤ X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hmono : ∫ t in (2 : ℝ)..X, 1 / Real.log X ≤ liX X := by
    unfold liX
    apply intervalIntegral.integral_mono_on hX2 intervalIntegrable_const (intervalIntegrable_inv_log_two hX2)
    intro t ht
    have ht0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  rw [mul_one_div, div_le_div_iff₀ (by linarith) hLX]
  nlinarith [mul_le_mul_of_nonneg_right hX hLX.le]

theorem liX_pow_le {X β δ : ℝ} (hX : 4 ≤ X) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1 - δ) :
    |liX (X ^ β)| ≤ 4 * Real.log X * Real.exp (-(δ * Real.log X)) * liX X := by
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hL]
  have hXpos : 0 < X := by linarith
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hXL : X = Real.exp L := by rw [hL, Real.exp_log hXpos]
  have hXb2 : 2 ≤ X ^ β := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = 4 ^ ((1 : ℝ) / 2) := h4.symm
      _ ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
  obtain ⟨h0, hup⟩ := liX_upper hXb2
  have hlow : X / (2 * L) ≤ liX X := by rw [hL]; exact liX_lower hX
  calc |liX (X ^ β)| = liX (X ^ β) := abs_of_nonneg h0
    _ ≤ 2 * X ^ β := hup
    _ = 2 * Real.exp (β * L) := by rw [Real.rpow_def_of_pos hXpos, ← hL, mul_comm L β]
    _ ≤ 2 * Real.exp ((1 - δ) * L) := by
        have : β * L ≤ (1 - δ) * L := mul_le_mul_of_nonneg_right hβ2 hL0.le
        have := Real.exp_le_exp.2 this
        linarith
    _ = 4 * L * Real.exp (-(δ * L)) * (X / (2 * L)) := by
        rw [hXL, show (1 - δ) * L = -(δ * L) + L by ring, Real.exp_add]
        field_simp
        ring
    _ ≤ 4 * L * Real.exp (-(δ * L)) * liX X :=
        mul_le_mul_of_nonneg_left hlow (by positivity)


theorem eventually_log_cube (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ x₂ : ℝ, ∀ x : ℝ, x₂ ≤ x → K * Real.log x ^ 3 ≤ x ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop 3 ha).bound (by positivity : (0 : ℝ) < 1 / K)
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x₂, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₂ x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 a)] at h1
  have h3 : Real.log x ^ 3 = Real.log x ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [h3]
  calc K * Real.log x ^ (3 : ℝ) ≤ K * |Real.log x ^ (3 : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hK.le
    _ ≤ K * (1 / K * x ^ a) := mul_le_mul_of_nonneg_left h1 hK.le
    _ = x ^ a := by field_simp

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

