module

public import Mathlib
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PrimeDiscriminants.BadCount
section
open NumberField

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem sum_bad_log_div_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S, Real.log p / ((p : ℝ) - 1) ≤
      S.card + 2 + 4 * Real.log H.rdE := by
  set U := Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S with hU
  have hprime : ∀ p ∈ U, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact hS p h
  have hterm1 : ∀ p ∈ U, Real.log p / ((p:ℝ) - 1) ≤ 1 := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    rw [div_le_one (by linarith)]
    exact Real.log_le_sub_one_of_pos (by linarith)
  have hterm2 : ∀ p ∈ U, Real.log p / ((p:ℝ) - 1) ≤ Real.log p := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    exact div_le_self (Real.log_natCast_nonneg p) (by linarith)
  rw [← Finset.sum_filter_add_sum_filter_not U (· ∈ H.small)]
  have hA : ∑ p ∈ U.filter (· ∈ H.small), Real.log p / ((p:ℝ) - 1) ≤ 4 * Real.log H.rdE := by
    calc _ ≤ ∑ p ∈ U.filter (· ∈ H.small), Real.log (p:ℝ) :=
          Finset.sum_le_sum fun p hp => hterm2 p (Finset.mem_filter.mp hp).1
      _ ≤ ∑ p ∈ H.small, Real.log (p:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
            (fun p _ _ => Real.log_natCast_nonneg p)
      _ ≤ _ := sum_small_log_le H
  have hB : ∑ p ∈ U.filter (· ∉ H.small), Real.log p / ((p:ℝ) - 1) ≤ S.card + 2 := by
    calc _ ≤ ∑ p ∈ U.filter (· ∉ H.small), (1:ℝ) :=
          Finset.sum_le_sum fun p hp => hterm1 p (Finset.mem_filter.mp hp).1
      _ = ((U \ H.small).card : ℝ) := by rw [Finset.sum_const, nsmul_one, Finset.sdiff_eq_filter]
      _ ≤ _ := by exact_mod_cast card_bad_sdiff_le H S
  linarith

end Formalism.BasicNotions.Host
end

-- bundled from Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr
section
open NumberField IsDedekindDomain Ideal

noncomputable section

namespace Formalism.HC

theorem dvd_discr_of_mem_sq (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → (p : 𝓞 E) ∈ P ^ 2) : (p : ℤ) ∣ discr E := by
  by_contra hd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  obtain ⟨P, hPm, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (span {(p : ℤ)})
  have hP := hPm.isPrime
  have hb : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hv : (p : 𝓞 E) ∈ P := by simpa using (Ideal.liesOver_span_iff hP.ne_top hpz).1 hlo
  have hun := (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd P hP (by simpa using hv)
  have hu : P.under ℤ = span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (P.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (P.under ℤ).ResidueField := inferInstance
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) = span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h P hP hv

theorem dvd_discr_of_sqrt (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {a : E} (ha : a ^ 2 = -(p : E)) :
    (p : ℤ) ∣ discr E := by
  have hi : IsIntegral ℤ a := IsIntegral.of_pow two_pos (ha ▸ (isIntegral_natCast p).neg)
  let b : 𝓞 E := ⟨a, hi⟩
  have hb : b ^ 2 = -(p : 𝓞 E) := RingOfIntegers.ext (by
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]; exact ha)
  refine dvd_discr_of_mem_sq E hp fun P hP hv => ?_
  have h1 : b ∈ P := hP.mem_of_pow_mem 2 (hb ▸ P.neg_mem hv)
  have h2 := (P ^ 2).neg_mem (Ideal.pow_mem_pow h1 2)
  rwa [hb, neg_neg] at h2

theorem HostAx.dvd_discr_of_dvd_QS {φ : Frame} (H : HostAx φ) (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) :
    (l : ℤ) ∣ discr H.E :=
  dvd_discr_of_mem_sq H.E hl fun P _ hv => H.mem_sq_of_dvd_QS hE hl hd P hv

end Formalism.HC

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem q_dvd_discr : (H.q : ℤ) ∣ discr H.E := Formalism.HC.dvd_discr_of_sqrt H.E H.q_prime H.sqq_sq

theorem dvd_discr_iff_dvd_condN {p : ℕ} (hp : p.Prime) : (p : ℤ) ∣ discr H.E ↔ p ∣ H.condN := by
  refine ⟨H.der.discr_primes.1 p hp, fun h => ?_⟩
  rcases (H.dvd_condN_iff hp).1 h with h | rfl | rfl
  · exact H.toHostAx.dvd_discr_of_dvd_QS H.QS_exact hp h
  · exact H.q_dvd_discr
  · exact H.der.discr_primes.2.2

theorem dvd_natAbs_discr_iff {p : ℕ} (hp : p.Prime) : p ∣ (discr H.E).natAbs ↔ p ∣ H.condN :=
  Int.natCast_dvd.symm.trans (H.dvd_discr_iff_dvd_condN hp)

end Formalism.BasicNotions.Host

end
end

