module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.FactorizationConductorLeLocalLevel
section
namespace UpperTheory.KStar.S0

open Formalism.BasicNotions

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem two_le_factorization (H : Host R) : 2 ≤ H.QS.factorization 2 := by
  have h1 := H.tower_dvd
  have h2 : 2 ^ (R.e + 2) ∣ H.QS := h1
  rw [Nat.prime_two.pow_dvd_iff_le_factorization H.QS_pos.ne'] at h2
  omega

theorem localLevel_eq_max_one_factorization : N.s0 i = max 1 (H.QS.factorization (N.l i)) := by
  by_cases h2 : N.l i = 2
  · have := two_le_factorization H
    rw [N.restNLevelExponent_of_two i h2, h2, max_eq_right (by omega)]
  · exact N.restNLevelExponent_of_odd i h2

theorem one_le_localLevel : 1 ≤ N.s0 i := by rw [localLevel_eq_max_one_factorization]; exact le_max_left _ _

theorem two_le_localLevel_of_eq_two (h : N.l i = 2) : 2 ≤ N.s0 i := by rw [N.restNLevelExponent_of_two i h]; exact two_le_factorization H

theorem factorization_conductor_le_localLevel : H.condN.factorization (N.l i) ≤ N.s0 i := by
  haveI := N.lPrime i
  have hl : (N.l i).Prime := Fact.out
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hqd : H.q ≠ H.d := by
    intro h
    rw [h] at hq8
    omega
  have hQS : H.QS ≠ 0 := H.QS_pos.ne'
  have hcop := H.QS_coprime
  have notdvd : N.l i ∣ H.q * H.d → ¬ N.l i ∣ H.QS := by
    intro h1 h2
    have h3 : N.l i ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd h2 h1
    rw [hcop] at h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  have e1 : H.condN.factorization (N.l i) =
      H.QS.factorization (N.l i) + (H.q.factorization (N.l i) + H.d.factorization (N.l i)) := by
    show (H.QS * H.q * H.d).factorization (N.l i) = _
    rw [mul_assoc, Nat.factorization_mul hQS (mul_ne_zero hq.ne_zero hd.ne_zero),
      Nat.factorization_mul hq.ne_zero hd.ne_zero]
    simp
  rw [e1, localLevel_eq_max_one_factorization N i, hq.factorization, hd.factorization, Finsupp.single_apply, Finsupp.single_apply]
  by_cases hlq : H.q = N.l i
  · have hz := Nat.factorization_eq_zero_of_not_dvd (notdvd (hlq ▸ dvd_mul_right _ _))
    have hdl : H.d ≠ N.l i := fun h => hqd (hlq.trans h.symm)
    rw [hz, if_pos hlq, if_neg hdl]
    exact le_max_left _ _
  · by_cases hld : H.d = N.l i
    · have hz := Nat.factorization_eq_zero_of_not_dvd (notdvd (hld ▸ dvd_mul_left _ _))
      rw [hz, if_neg hlq, if_pos hld]
      exact le_max_left _ _
    · rw [if_neg hlq, if_neg hld]
      simp

end UpperTheory.KStar.S0
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
section
namespace UpperTheory.Small

open Formalism.BasicNotions

variable {R : Ranks} (H : Host R)

theorem two_mem : 2 ∈ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  refine ⟨Nat.prime_two, ?_, (H.QS_pos).ne'⟩
  have he : 2 ≤ R.e := H.two_le_e
  exact dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd

theorem ne_two {l : ℕ} (h : l ∉ H.small) : l ≠ 2 := by
  rintro rfl
  exact h (two_mem H)

theorem not_mem_of_dvd_qd {l : ℕ} (hl : l ∣ H.q * H.d) : l ∉ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  rintro ⟨hp, hdq, -⟩
  have h1 : l ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdq hl
  rw [H.QS_coprime.gcd_eq_one] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem q_not_mem : H.q ∉ H.small := not_mem_of_dvd_qd H (dvd_mul_right _ _)

theorem d_not_mem : H.d ∉ H.small := not_mem_of_dvd_qd H (dvd_mul_left _ _)

theorem not_mem_of_qd {l : ℕ} (hl : l = H.q ∨ l = H.d) : l ∉ H.small := by
  rcases hl with rfl | rfl
  · exact q_not_mem H
  · exact d_not_mem H

theorem not_mem_of_mod {l : ℕ} (h : l % (H.QS * H.q * H.d) = 1) : l ∉ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  rintro ⟨hp, hdq, -⟩
  have hm : l ∣ H.QS * H.q * H.d := dvd_trans hdq (by rw [mul_assoc]; exact dvd_mul_right _ _)
  have h1 : l ∣ l % (H.QS * H.q * H.d) := (Nat.dvd_mod_iff hm).2 dvd_rfl
  rw [h] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem factorization_eq_zero {l : ℕ} (h : l ∉ H.small) : H.QS.factorization l = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  by_contra hc
  push_neg at hc
  apply h
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  exact ⟨hc.1, hc.2.1, hc.2.2⟩

variable {H} in
theorem localLevel_eq_one_of_not_mem_smallPrimes {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.l i ∉ H.small) : N.s0 i = 1 := by
  rw [N.restNLevelExponent_of_odd i (ne_two H h), factorization_eq_zero H h]; rfl

end UpperTheory.Small
end

