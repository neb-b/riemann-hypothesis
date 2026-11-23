module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VectorsLinearMapsBoundedDenominatorsAtPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime

theorem exists_intAt_pow_mul {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * a) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  have h1 : P.valuation E (qOf P : E) < 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key : ∃ m : ℕ, P.valuation E ((qOf P : E) ^ m * a) ≤ 1 := by
    rcases eq_or_ne (P.valuation E a) 0 with ha | ha
    · exact ⟨0, by simp [ha]⟩
    have hq : P.valuation E (qOf P : E) ≠ 0 := by
      simpa using GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
    refine ⟨(WithZero.log (P.valuation E a)).toNat, ?_⟩
    rw [map_mul, map_pow]
    rw [← WithZero.exp_log hq, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_log hq, ← WithZero.exp_log ha, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
    set u := WithZero.log (P.valuation E (qOf P : E))
    set w := WithZero.log (P.valuation E a)
    have h2 : w ≤ (w.toNat : ℤ) := Int.self_le_toNat w
    have h3 : (0 : ℤ) ≤ (w.toNat : ℤ) := Int.natCast_nonneg _
    rw [nsmul_eq_mul]
    nlinarith
  obtain ⟨m, h⟩ := key
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer _ h
  exact ⟨m, n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem exists_intAt_family {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ i, IntAt P ((qOf P : E) ^ m' * f i) := by
  choose g hg using fun i => exists_intAt_pow_mul P (f i)
  exact ⟨Finset.univ.sup g, fun m' hm i =>
    GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono ((Finset.le_sup (Finset.mem_univ i)).trans hm) (hg i)⟩

theorem bounded_denominators : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  intro E _ _ P a b
  refine ⟨fun v => ?_, fun y => ?_⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P v
    exact ⟨m, fun m' h l => hm m' h l⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P (fun p : Fin a × Fin b => y (Pi.single p.1 1) p.2)
    exact ⟨m, fun m' h => (intHom_iff _).2 fun s l => hm m' h (s, l)⟩

end GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedBoxSumAtPrimeEqOfBoundedSchwartz
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory

theorem boxSum_eq_of_funBdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  intro E _ _ K _ _ P hq ι _ _ f N hf A B hA hB
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  unfold boxSum
  refine weighted_sum_piFinset ι E K
    (fun g => (∀ a, g a ≠ 0 → IntAt P ((qOf P : E) ^ N * a)) ∧
      ∀ a u, IntAt P u → g (a + (qOf P : E) ^ N * u) = g a) _ _ _ _ ?_ f ?_
  · rintro g ⟨h1, h2⟩
    rw [sum_valsQ_of_invariant E P K g N h2 A B hB,
      sum_valsQ_eq_of_support_intAt E P hq K g N h1 A N hA]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  · intro t i
    refine ⟨fun a ha => ?_, fun a u hu => ?_⟩
    · simpa using hf.1 _ ha i
    · have e : Function.update t i (a + (qOf P : E) ^ N * u)
          = Function.update t i a + ((qOf P : E) ^ N) • (Pi.single i u : ι → E) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      simp only [e]
      refine hf.2 _ _ fun j => ?_
      by_cases hj : j = i
      · subst hj; simpa using hu
      · simpa [hj] using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

end GlobalTheory
end

