module

public import Mathlib
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0008
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0002
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0009
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0007
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0005
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.BadLog
section
open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.KR.sum_log_bad_le :
    ∀ {φ : Frame} (H : HostAx φ) (M : ℕ) (S : Finset ℕ), M ≠ 0 →
      (∀ p ∈ S, p.Prime ∧ (p = 2 ∨ p = H.d ∨ p ∣ (discr H.E).natAbs ∨ p ∣ M)) →
        ∑ p ∈ S, Real.log p ≤ 2 * Real.log H.rd + Real.log M := by
  intro φ H M S hM hS
  have hD : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero H.E)
  obtain ⟨hA, hB, -⟩ := UpperTheory.HF.ram_eq H
  have hsub : S ⊆ H.ram ∪ M.primeFactors := by
    intro p hp
    obtain ⟨hpp, h⟩ := hS p hp
    rw [Finset.mem_union]
    rcases h with h | h | h | h
    · exact Or.inl ((hA p).2 (Or.inl (h ▸ hB)))
    · exact Or.inl ((hA p).2 (Or.inr (Or.inr h)))
    · exact Or.inl (Nat.mem_primeFactors.2 ⟨hpp, h, hD⟩)
    · exact Or.inr (Nat.mem_primeFactors.2 ⟨hpp, h, hM⟩)
  have h1 : ∑ l ∈ H.ram, Real.log l ≤ 2 * Real.log H.rd := by
    simpa using (UpperTheory.HF.rad_bounds2 H).1 0 1 le_rfl zero_le_one
  have h2 : ∑ l ∈ M.primeFactors, Real.log l ≤ Real.log M := by
    have hne : ∀ l ∈ M.primeFactors, (l : ℝ) ≠ 0 := fun l hl =>
      Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hl).ne_zero
    rw [← Real.log_prod hne, ← Nat.cast_prod]
    refine Real.log_le_log ?_ ?_
    · exact Nat.cast_pos.2 (Finset.prod_pos fun l hl => (Nat.prime_of_mem_primeFactors hl).pos)
    · exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.prod_primeFactors_dvd M))
  have h3 : ∑ p ∈ S, Real.log p ≤ ∑ p ∈ H.ram ∪ M.primeFactors, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => Real.log_natCast_nonneg p
  have h4 := Finset.sum_union_inter (s₁ := H.ram) (s₂ := M.primeFactors) (f := fun p : ℕ => Real.log p)
  have h5 : 0 ≤ ∑ p ∈ H.ram ∩ M.primeFactors, Real.log p :=
    Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  linarith
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.HalfNorm
section
open UpperTheory.HF

open NumberField Ideal
open scoped Pointwise

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem mem_ramI_iff {p : ℕ} (hp : p.Prime) : p ∈ H.toHostRaw.ramI ↔ p ∣ H.QS * H.q := by
  have h0 : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  rw [Formalism.HC.HostRaw.ramI, Finset.mem_erase, Formalism.HC.HostRaw.ram, Nat.mem_primeFactors, H.dvd_natAbs_discr_iff hp]
  constructor
  · rintro ⟨hd, -, h, -⟩
    exact ((Nat.Prime.dvd_mul hp).1 h).resolve_right fun h' =>
      hd ((Nat.prime_dvd_prime_iff_eq hp H.toHostRaw.d_prime).1 h')
  · intro h
    refine ⟨?_, hp, h.mul_right _, h0⟩
    rintro rfl
    exact H.toHostRaw.d_not_dvd_QSq h

private theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) : P.LiesOver (span {(p : ℤ)}) :=
  ⟨Ideal.IsMaximal.eq_of_le
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible)
    (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]; exact h)⟩

private theorem dvd_absNorm_of {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P J : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) (hJ : P ∣ J) : p ∣ absNorm J := by
  by_contra hn
  obtain ⟨u, v, huv⟩ : IsCoprime (p : 𝓞 E) ((absNorm J : ℕ) : 𝓞 E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn).cast
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2
    (huv ▸ P.add_mem (P.mul_mem_left u h) (P.mul_mem_left v (Ideal.le_of_dvd hJ (Ideal.absNorm_mem J)))))

theorem half_ne_bot : H.𝔟 ≠ ⊥ := fun h => by
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem prime_dvd_absNorm_half_iff {p : ℕ} (hp : p.Prime) : p ∣ absNorm H.𝔟 ↔ p ∣ H.QS * H.q := by
  have hs := (UpperTheory.HF.half_supp H.toHostAx H.𝔟 H.𝔟_spec.1 H.𝔟_spec.2).1
  constructor
  · intro h
    obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h
    haveI := hP.isPrime
    obtain ⟨l, hl, ho⟩ := (hs P).1.1 (Or.inl hd)
    have hlp : l.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
    have e : span {(l : ℤ)} = span {(p : ℤ)} := ho.over.trans hu
    have : p ∣ l := by
      have := Ideal.mem_span_singleton.1 (e ▸ Ideal.mem_span_singleton_self (l : ℤ))
      exact_mod_cast this
    rw [(Nat.prime_dvd_prime_iff_eq hp hlp).1 this]
    exact (H.mem_ramI_iff hlp).1 hl
  · intro h
    have h1 : p ∣ absNorm (span {(p : 𝓞 H.E)}) := by
      rw [Ideal.absNorm_span_natCast]
      exact dvd_pow_self _ Module.finrank_pos.ne'
    obtain ⟨P, hP, -, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h1
    haveI := hP.isPrime
    have hm : (p : 𝓞 H.E) ∈ P := Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)
    rcases (hs P).1.2 ⟨p, (H.mem_ramI_iff hp).2 h, liesOver_of_mem hp P hm⟩ with h2 | h2
    · exact dvd_absNorm_of hp P _ hm h2
    · have hm' : (p : 𝓞 H.E) ∈ H.toHostRaw.conj • P := by
        have := Ideal.smul_mem_pointwise_smul H.toHostRaw.conj _ _ hm
        rwa [show H.toHostRaw.conj • (p : 𝓞 H.E) = p from map_natCast (MulSemiringAction.toRingHom _ (𝓞 H.E) H.toHostRaw.conj) p] at this
      exact dvd_absNorm_of hp _ _ hm' h2

theorem four_ord_le_condN : 4 * R.toFrame.ord ≤ H.QS * H.q * H.d := by
  have h := UpperTheory.HF.cond_rd H.toHostAx
  have h2 := UpperTheory.HF.ram_eq H.toHostAx
  refine h.2.2.2.2.2.2.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero) ?_)
  rw [h2.2.2.2.1]
  refine Nat.mul_dvd_mul_right (Nat.mul_dvd_mul h2.2.2.2.2.1 ?_) _
  split_ifs
  exacts [dvd_rfl, one_dvd _]

end Formalism.BasicNotions.Host
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
section
open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.KR.log_qd_le_rd :
    ∀ {φ : Frame} (H : HostAx φ), H.toHostRaw.PsQ → H.q ∈ H.ram ∧ Real.log H.q + Real.log H.d ≤ 2 * Real.log H.rd ∧ Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd ∧ 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
  intro φ H hP
  have hq : H.q ∈ H.ram := (UpperTheory.HF.inert_q H).2.2.2.2 hP
  obtain ⟨hA, hB, -⟩ := UpperTheory.HF.ram_eq H
  have hd : H.d ∈ H.ram := (hA _).2 (Or.inr (Or.inr rfl))
  have h2 : 2 ∈ H.ram := (Finset.mem_inter.1 hB).2
  obtain ⟨hs, -, -, hrd⟩ := UpperTheory.HF.log_rd_sum H
  have vq : 1 / 2 ≤ H.vdH H.q := (UpperTheory.HF.mem_ram H H.q_prime).2.2.2.1 hq
  have vd : 1 / 2 ≤ H.vdH H.d := (UpperTheory.HF.mem_ram H H.d_prime).2.2.2.1 hd
  have v2 : 11 / 4 ≤ H.vdH 2 := (UpperTheory.HF.vd_two H).2.1
  have n2q : 2 ≠ H.q := fun h => H.q_notMem_small (h ▸ H.two_mem_small)
  have n2d : 2 ≠ H.d := fun h => H.d_notMem_small (h ▸ H.two_mem_small)
  have nqd : H.q ≠ H.d := H.q_ne_d
  have hsub : ({2, H.q, H.d} : Finset ℕ) ⊆ H.ram := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l : ℕ => H.vdH l * Real.log l) hsub
    (fun l _ _ => mul_nonneg (H.vdH_nonneg l) (Real.log_natCast_nonneg l))
  rw [← hs, Finset.sum_insert (by simp [n2q, n2d]), Finset.sum_pair nqd] at hle
  have lq := Real.log_natCast_nonneg H.q
  have ld := Real.log_natCast_nonneg H.d
  have l2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq0 : (0 : ℝ) < H.q := Nat.cast_pos.2 H.q_prime.pos
  have hd0 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  push_cast at hle
  have key : Real.log 2 + (Real.log H.q + Real.log H.d) / 2 ≤ Real.log H.rd := by
    nlinarith [mul_le_mul_of_nonneg_right vq lq, mul_le_mul_of_nonneg_right vd ld,
      mul_le_mul_of_nonneg_right v2 l2.le]
  have hsq : 0 < Real.sqrt ((H.q : ℝ) * H.d) := Real.sqrt_pos.2 (mul_pos hq0 hd0)
  have h4 : 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
    rw [← Real.log_le_log_iff (by positivity) hrd, Real.log_mul two_ne_zero hsq.ne',
      Real.log_sqrt (mul_pos hq0 hd0).le, Real.log_mul hq0.ne' hd0.ne']
    exact key
  exact ⟨hq, by linarith, by linarith, h4⟩
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OrdLeTotientQS
section
theorem UpperTheory.Ram.ord_le_totient_QS :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), φ.ord ≤ H.QS.totient ∧ 2 * φ.ord ≤ H.QS := by
  intro φ H
  obtain ⟨h1, h2, -⟩ := UpperTheory.KR.two_ord_le_QS H
  exact ⟨h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.SmallVdSum
section
open NumberField Formalism.HC

theorem UpperTheory.KR.small_vd_sum :
    ∀ {φ : Frame} (H : HostAx φ), (∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p ≤ 3 / 2 * Real.logb 2 H.QS) ∧ 2 ∈ H.small ∧
      ∀ r : ℕ, r.Prime → r ∉ H.small → r ≠ H.q → r ≠ H.d → ¬ (r : ℤ) ∣ discr H.E := by
  intro φ H
  obtain ⟨hsm, -, -, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds H
  refine ⟨?_, H.two_mem_small, ?_⟩
  · have hQ0 : H.QS ≠ 0 := H.QS_ne_zero
    have hlogQ : Real.log (H.QS : ℝ) = ∑ p ∈ H.small, (padicValNat p H.QS : ℝ) * Real.log p := by
      show _ = ∑ p ∈ H.QS.primeFactors, (padicValNat p H.QS : ℝ) * Real.log p
      have hprod : (H.QS : ℝ) = ∏ p ∈ H.QS.primeFactors, (p : ℝ) ^ (H.QS.factorization p) := by
        conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hQ0]
        rw [Finsupp.prod, Nat.support_factorization]
        push_cast
        rfl
      rw [hprod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Real.log_pow, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp),
          ← Nat.padicValNat_def]
      · intro p hp
        exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have hlog2 : Real.log (H.QS : ℝ) ≤ Real.logb 2 H.QS := by
      rw [Real.logb]
      have hl0 : 0 ≤ Real.log (H.QS : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2' : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      rw [le_div_iff₀ h2]
      nlinarith
    calc ∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p
        ≤ ∑ p ∈ H.small, 3 / 2 * ((padicValNat p H.QS : ℝ) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpp, hpd⟩ := (H.mem_small_iff).mp hp
          haveI := Fact.mk hpp
          have hv1 : (1 : ℝ) ≤ padicValNat p H.QS := by
            exact_mod_cast (by simpa only [Nat.padicValNat_def] using one_le_padicValNat_of_dvd hQ0 hpd)
          have hvd := (hsm p hp).1
          have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 * padicValNat p H.QS - 1 - H.vdH p / 2) hlp]
      _ = 3 / 2 * Real.log H.QS := by rw [hlogQ, Finset.mul_sum]
      _ ≤ 3 / 2 * Real.logb 2 H.QS := by linarith
  · intro r hr hrs hrq hrd hdvd
    have h : r ∣ H.QS * H.q * H.d := (H.der.discr_primes).1 r hr hdvd
    rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
      · exact hrs ((H.mem_small_iff).mpr ⟨hr, h2⟩)
      · exact hrq ((Nat.prime_dvd_prime_iff_eq hr H.q_prime).mp h2)
    · exact hrd ((Nat.prime_dvd_prime_iff_eq hr H.d_prime).mp h1)
end

