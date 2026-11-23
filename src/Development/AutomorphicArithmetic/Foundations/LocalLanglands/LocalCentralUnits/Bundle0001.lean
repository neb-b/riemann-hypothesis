module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinFld

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsoUniq
section
open ValuativeRel Filter

private theorem val_natCast_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* k) (hi : Continuous i) :
    valuation k (g : k) < 1 := by
  have h1 : Tendsto (fun m : ℕ => (g : ℚ_[g]) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have hT : Tendsto (fun m : ℕ => i ((g : ℚ_[g]) ^ m)) atTop (nhds 0) := by
    have := (hi.tendsto 0).comp h1
    rwa [map_zero] at this
  have hopen : IsOpen {x : k | valuation k x < 1} := by
    simpa [Valuation.restrict_lt_one_iff] using (valuation k).isOpen_ball 1
  have hO : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    hopen.mem_nhds (by simp)
  obtain ⟨m, hm, hm0⟩ := ((hT.eventually hO).and (eventually_gt_atTop 0)).exists
  have hm' : valuation k (g : k) ^ m < 1 := by
    have : valuation k (i ((g : ℚ_[g]) ^ m)) < 1 := hm
    rwa [map_pow, map_natCast, map_pow] at this
  by_contra hge
  exact absurd hm' (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))

private theorem val_intCast_le_one {k : Type} [Field k] [ValuativeRel k] (a : ℤ) :
    valuation k (a : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (intCast_mem (valuation k).integer a)

theorem UpperTheory.Zero.LLC.isoUniq :
    UpperTheory.Zero.LLC.IsoUniq := by
  intro k _ _ _ _ _ g g' _ _ i i' hi hi'
  refine ⟨?_, fun i'' hi'' => ?_⟩
  · by_contra hne
    have hc : Nat.Coprime g g' := (Nat.coprime_primes Fact.out Fact.out).2 hne
    have hb : ((1 : ℤ) : k) = (g : k) * (Nat.gcdA g g' : k) + (g' : k) * (Nat.gcdB g g' : k) := by
      have h := Nat.gcd_eq_gcd_ab g g'
      rw [hc.gcd_eq_one] at h
      exact_mod_cast congrArg (Int.cast : ℤ → k) h
    have hv : valuation k (1 : k) < 1 := by
      have h1 : ((1 : ℤ) : k) = 1 := Int.cast_one
      rw [← h1, hb]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g i hi) (val_intCast_le_one _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g' i' hi') (val_intCast_le_one _)
    rw [map_one] at hv
    exact lt_irrefl _ hv
  · have h : (i'' : ℚ_[g] → k) = i :=
      (Padic.denseRange_ratCast g).equalizer hi'' hi (by
        funext q
        simp only [Function.comp_apply, map_ratCast])
    exact DFunLike.coe_injective h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PairCheckThreeTwo
section
open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

private def Reg (g n N t : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, (t * g ^ i) % N = (t * g ^ j) % N → i = j

private def Cl (g n N e t : ℕ) : Prop :=
  ∀ i < n, ∃ j < n, (t * g ^ i + e) % N = (t * g ^ j) % N

private instance (g n N t : ℕ) : Decidable (Reg g n N t) := by
  unfold Reg
  infer_instance

private instance (g n N e t : ℕ) : Decidable (Cl g n N e t) := by
  unfold Cl
  infer_instance

private def Pair (g n N e t t' : ℕ) : Prop :=
  (Reg g n N t ∧ Cl g n N e t) → (Reg g n N t' ∧ Cl g n N e t') → ∃ j < n, t' % N = (t * g ^ j) % N

private instance (g n N e t t' : ℕ) : Decidable (Pair g n N e t t') := by
  unfold Pair
  infer_instance

private theorem pairCheck_two_two : ∀ t < 2 ^ 2 - 1, ∀ t' < 2 ^ 2 - 1, Pair 2 2 (2 ^ 2 - 1) 1 t t' := by
  decide

private theorem pairCheck_three_two : ∀ t < 3 ^ 2 - 1, ∀ t' < 3 ^ 2 - 1, Pair 3 2 (3 ^ 2 - 1) 2 t t' := by
  decide

set_option maxHeartbeats 4000000 in
private theorem pairCheck_two_four : ∀ t < 2 ^ 4 - 1, ∀ t' < 2 ^ 4 - 1, Pair 2 4 (2 ^ 4 - 1) 3 t t' := by
  decide

set_option maxHeartbeats 40000000 in
private theorem pairCheck_two_six : ∀ t < 2 ^ 6 - 1, ∀ t' < 2 ^ 6 - 1, Pair 2 6 (2 ^ 6 - 1) 21 t t' := by
  decide

section

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem card_unitsK [Fintype Kˣ] (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) :
    Fintype.card Kˣ = g ^ n - 1 := by
  rw [Fintype.card_eq_nat_card, Nat.card_units, natCard_K hn hr]

private theorem exc (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (e : ℕ)
    (he : ∀ p ∈ n.primeFactors, (g ^ (n / p) - 1) ∣ e)
    (hcheck : ∀ t < g ^ n - 1, ∀ t' < g ^ n - 1, Pair g n (g ^ n - 1) e t t')
    (θ θ' : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j)
    (hθ' : ∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j)
    (hs : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  by_contra hne
  have hdisj := disj_cj hn hr θ θ' hne
  obtain ⟨D, hD1, hD2, -⟩ := exists_D (K := K) (g := g) hn hr
  have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
    intro z hz
    unfold dif
    rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
  obtain ⟨η₀, hgen, hpow⟩ := exists_gen_char (G := Kˣ)
  have hcard := card_unitsK (K := K) (g := g) hn hr
  rw [hcard] at hgen hpow
  have key : ∀ s : ℕ, (∀ i j, i < n → j < n → (η₀ ^ s) ^ g ^ i = (η₀ ^ s) ^ g ^ j → i = j) →
      (∀ ψ ∈ cj g n (η₀ ^ s), ψ * η₀ ^ e ∈ cj g n (η₀ ^ s)) →
      Reg g n (g ^ n - 1) s ∧ Cl g n (g ^ n - 1) e s := by
    intro s hreg hcl
    unfold Reg Cl
    refine ⟨fun i hi j hj hij => hreg i j hi hj ?_, fun i hi => ?_⟩
    · rw [← pow_mul, ← pow_mul, hpow]
      exact hij
    · have hm : (η₀ ^ s) ^ g ^ i ∈ cj g n (η₀ ^ s) := mem_cj.2 ⟨i, hi, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := mem_cj.1 (hcl _ hm)
      refine ⟨j, hj, ?_⟩
      rw [← pow_mul, ← pow_mul, ← pow_add, hpow] at hjeq
      exact hjeq.symm
  have hηD : ∀ z ∈ D, (η₀ ^ e) z = 1 := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := hD2 z hz
    obtain ⟨c, hc⟩ := he p hp
    rw [MonoidHom.pow_apply, ← map_pow, hc, pow_mul, hzp, one_pow, map_one]
  have hmm := mul_mem _ _ hdisj D hdif (η₀ ^ e) hηD
  obtain ⟨t, ht, rfl⟩ := hgen θ
  obtain ⟨t', ht', rfl⟩ := hgen θ'
  have hP := hcheck t ht t' ht'
  unfold Pair at hP
  obtain ⟨j, hj, hjt⟩ := hP (key t hθ (fun ψ hψ => (hmm ψ).1 hψ))
    (key t' hθ' (fun ψ hψ => (hmm ψ).2 hψ))
  exact hne ⟨j, hj, by rw [← pow_mul, hpow]; exact hjt⟩

private theorem main (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) :
    (∃ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n ∧
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) ≠ 0) ∧
    ∀ θ' : Kˣ →* ℂˣ, (∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j) →
      (∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
        ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) →
      ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hcard := card_unitsK (K := K) (g := g) hn hr
  obtain ⟨D, hD1, hD2, hDb⟩ := exists_D (K := K) (g := g) hn hr
  have hA := card_cj hθ
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    have hdif : ∀ z ∉ D, dif (cj g n θ) ∅ z = 0 := by
      intro z hz
      unfold dif
      rw [sum_cj hθ, hno z (hD1 z hz)]
      simp
    have hle := card_le (cj g n θ) ∅ (Finset.disjoint_empty_right _) D hdif (by simp [hA, hn])
    rw [hA, hcard] at hle
    simp only [Finset.card_empty, add_zero] at hle
    have h1 := one_bd g n hg2 hn
    have h2 : D.card * n ≤ n * bd g n := by
      rw [mul_comm n]
      exact Nat.mul_le_mul_right n hDb
    omega
  · intro θ' hθ' hs
    by_cases hex : g = 2 ∧ n = 2 ∨ g = 3 ∧ n = 2 ∨ g = 2 ∧ n = 4 ∨ g = 2 ∧ n = 6
    · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine exc hn hr 1 ?_ pairCheck_two_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 2 ?_ pairCheck_three_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 3 ?_ pairCheck_two_four θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 21 ?_ pairCheck_two_six θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
    · by_contra hne
      have hB := card_cj hθ'
      have hdisj := disj_cj hn hr θ θ' hne
      have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
        intro z hz
        unfold dif
        rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
      have hle := card_le _ _ hdisj D hdif (by rw [hA, hB]; omega)
      rw [hA, hB, hcard] at hle
      have h1 := two_bd g n hg2 hn hex
      have h2 : D.card * (n + n) ≤ 2 * n * bd g n := by
        calc D.card * (n + n) ≤ bd g n * (n + n) := Nat.mul_le_mul_right _ hDb
          _ = 2 * n * bd g n := by ring
      omega

end

end UpperTheory.Zero.LLC.CharacterSumPairs

theorem UpperTheory.Zero.LLC.pin :
    UpperTheory.Zero.LLC.Pin := by
  unfold UpperTheory.Zero.LLC.Pin
  intro g _ n hn K _ _ hr θ hθ
  exact UpperTheory.Zero.LLC.CharacterSumPairs.main hn hr θ hθ
end

