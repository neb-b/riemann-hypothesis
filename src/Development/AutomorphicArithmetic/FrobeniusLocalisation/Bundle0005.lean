module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0004
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0002
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0003
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DvdDiscrOfInertia

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.LayerBot
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem layer_dvd {N l j : ℕ} (hj : j ≤ N.factorization l) : ordCompl[l] N * l ^ j ∣ N := by
  have h := Nat.ordProj_mul_ordCompl_eq_self N l
  conv_rhs => rw [← h, mul_comm]
  exact mul_dvd_mul_left _ (pow_dvd_pow l hj)

private theorem dvd_layer_iff {N c l j : ℕ} (hl : l.Prime) (hN : N ≠ 0) (hc : c ∣ N) :
    c ∣ ordCompl[l] N * l ^ j ↔ c.factorization l ≤ j := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hc)
  have hM : 0 < ordCompl[l] N := Nat.ordCompl_pos l hN
  have hM0 : ordCompl[l] N * l ^ j ≠ 0 := Nat.mul_ne_zero hM.ne' (pow_ne_zero _ hl.ne_zero)
  have hfM : (ordCompl[l] N * l ^ j).factorization = N.factorization.erase l + Finsupp.single l j := by
    rw [Nat.factorization_mul hM.ne' (pow_ne_zero _ hl.ne_zero), Nat.factorization_ordCompl,
      hl.factorization_pow]
  have hcN := (Nat.factorization_le_iff_dvd hc0 hN).2 hc
  rw [← Nat.factorization_le_iff_dvd hc0 hM0, hfM]
  constructor
  · intro h
    have := h l
    simpa using this
  · intro h q
    by_cases hq : q = l
    · subst hq
      simpa using h
    · rw [Finsupp.add_apply, Finsupp.erase_ne hq]
      exact le_add_right (hcN q)

theorem UpperTheory.HF.layer_bot :
    ∀ {φ : Frame} (H : HostRaw φ) {l j : ℕ}, l.Prime → j ≤ H.condN.factorization l → (H.imgOne (ordCompl[l] H.condN * l ^ j) = ⊥ ↔ H.condE.factorization l ≤ j) ∧ (j ≤ H.condE.factorization l → Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) ∣ (l ^ H.condE.factorization l).totient / (l ^ j).totient) ∧ H.condE.factorization l ≤ H.condN.factorization l := by
  intro φ H l j hl hj
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  obtain ⟨hE, hEpos, hspec⟩ := condE_spec H
  have hEN : H.condE.factorization l ≤ H.condN.factorization l :=
    (Nat.factorization_le_iff_dvd hEpos.ne' hN).2 hE l
  have part1 : ∀ k, k ≤ H.condN.factorization l →
      (H.imgOne (ordCompl[l] H.condN * l ^ k) = ⊥ ↔ H.condE.factorization l ≤ k) := by
    intro k hk
    rw [hspec _ (layer_dvd hk)]
    exact dvd_layer_iff hl hN hE
  refine ⟨part1 j hj, fun hje => ?_, hEN⟩
  set e := H.condE.factorization l with he
  have hdiv : ordCompl[l] H.condN * l ^ j ∣ ordCompl[l] H.condN * l ^ e :=
    mul_dvd_mul_left _ (pow_dvd_pow l hje)
  have hc := card_imgOne_dvd H hdiv (layer_dvd hEN)
  rw [(part1 e hEN).2 le_rfl, Subgroup.card_bot, one_mul] at hc
  have hcop : ∀ k, (ordCompl[l] H.condN).Coprime (l ^ k) := fun k =>
    ((Nat.coprime_ordCompl hl hN).pow_left k).symm
  have hM : 0 < ordCompl[l] H.condN := Nat.ordCompl_pos l hN
  rw [Nat.totient_mul (hcop e), Nat.totient_mul (hcop j),
    Nat.mul_div_mul_left _ _ (Nat.totient_pos.2 hM)] at hc
  exact hc
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.VdTwo
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem rho_sum {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {e : ℕ} (h2 : 2 ^ (e + 2) ∣ N)
    (hU : ∀ u ∈ U, ZMod.unitsMap h2 u = 1 ∨ ZMod.unitsMap h2 u = -1) :
    (e : ℝ) + 1 - 1 / 2 ^ e ≤
      ∑ j ∈ Finset.range (N.factorization 2), Formalism.HC.Der.Rd.rho U (ordCompl[2] N * 2 ^ j) := by
  have hN : N ≠ 0 := NeZero.ne N
  have ha : e + 2 ≤ N.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN).1 h2
  have hM : Nat.Coprime 2 (ordCompl[2] N) := Nat.coprime_ordCompl Nat.prime_two hN
  have hdvd : 2 ^ (e + 2) * ordCompl[2] N ∣ N := by
    have h := mul_dvd_mul_right (pow_dvd_pow 2 ha) (ordCompl[2] N)
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at h
  have ht : ∑ j ∈ Finset.range (e + 2), (((2 ^ j).totient : ℕ) : ℝ) = 2 ^ (e + 1) := by
    have h := Formalism.HC.Der.Rd.sum_totient_pow Nat.prime_two (e + 1)
    rw [show e + 1 + 1 = e + 2 by ring] at h
    exact_mod_cast h
  have hc : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 2), (if j < 2 then (1:ℝ) else 0) = 2 := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.sum_range_succ, ih]
      simp
  calc (e : ℝ) + 1 - 1 / 2 ^ e
      = ∑ j ∈ Finset.range (e + 2),
          (1 - ((((2 ^ j).totient : ℕ) : ℝ) + if j < 2 then 1 else 0) / 2 ^ (e + 1)) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ht, hc e]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        push_cast
        field_simp
        ring
    _ ≤ ∑ j ∈ Finset.range (e + 2), Formalism.HC.Der.Rd.rho U (ordCompl[2] N * 2 ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j ≤ e + 2 := (Finset.mem_range.1 hj).le
        rw [mul_comm]
        exact Formalism.HC.Der.Rd.rho_two U hM hdvd hj' hU
    _ ≤ ∑ j ∈ Finset.range (N.factorization 2), Formalism.HC.Der.Rd.rho U (ordCompl[2] N * 2 ^ j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ha)
          (fun _ _ _ => Formalism.HC.Der.Rd.rho_nonneg _ _)

theorem UpperTheory.HF.vd_two :
    ∀ {φ : Frame} (H : HostAx φ), (φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ)) ≤ H.vdH 2 ∧ 11 / 4 ≤ H.vdH 2 ∧ 4 + 2 * H.vdH 2 ≤ 2 + 3 * H.vdH 2 := by
  intro φ H
  haveI : NeZero H.condN := ⟨by
    have h := H.QS_pos
    have hq := (HostRaw.q_prime H.toHostRaw).pos
    have hd := (HostRaw.d_prime H.toHostRaw).pos
    show H.QS * H.q * H.d ≠ 0
    positivity⟩
  have hU : ∀ u ∈ H.art.ker, ZMod.unitsMap (Formalism.HC.Der.Rd.two_dvd H.toHostRaw) u = 1 ∨
      ZMod.unitsMap (Formalism.HC.Der.Rd.two_dvd H.toHostRaw) u = -1 := by
    intro u hu
    apply Formalism.HC.Der.Rd.hcl_eq_one
    rw [← Formalism.HC.Der.Rd.hH_art, MonoidHom.mem_ker.1 hu]
    exact map_one _
  have hs := rho_sum H.art.ker (Formalism.HC.Der.Rd.two_dvd H.toHostRaw) hU
  have hv : H.vdH 2 = ∑ j ∈ Finset.range (H.condN.factorization 2),
      Formalism.HC.Der.Rd.rho H.art.ker (ordCompl[2] H.condN * 2 ^ j) := by
    rw [vd_formula H Nat.prime_two]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rho_art H.toHostRaw]
    apply Nat.dvd_trans (Nat.mul_dvd_mul_left _ (pow_dvd_pow 2 (Finset.mem_range.1 hj).le))
    rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  have he : 2 ≤ φ.e := H.two_le_e
  have hrp : (2 : ℝ) ^ (-(φ.e : ℝ)) = 1 / 2 ^ φ.e := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
  have h4 : (4 : ℝ) ≤ 2 ^ φ.e := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ φ.e := pow_le_pow_right₀ (by norm_num) he
  have hinv : 1 / (2 : ℝ) ^ φ.e ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
  have hecast : (2 : ℝ) ≤ φ.e := by exact_mod_cast he
  have hmain : (φ.e : ℝ) + 1 - 1 / 2 ^ φ.e ≤ H.vdH 2 := by rw [hv]; exact hs
  rw [hrp]
  refine ⟨hmain, ?_, ?_⟩ <;> linarith
end

