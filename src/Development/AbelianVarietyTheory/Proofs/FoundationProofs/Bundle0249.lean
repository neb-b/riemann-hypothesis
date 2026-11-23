module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorCmDifferentIdealScaled
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.IdealGenerator

theorem coe_ideal_mul {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (I : FractionalIdeal R⁰ K) :
    (((P : FractionalIdeal R⁰ K) * I : FractionalIdeal R⁰ K) : Submodule R K) = P • (I : Submodule R K) := by
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_coeIdeal]
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨p, hp, rfl⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hm
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul hp hn
  · rw [Submodule.smul_le]
    intro p hp n hn
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ((IsLocalization.mem_coeSubmodule _ _).2 ⟨p, hp, rfl⟩) hn

theorem exists_gen {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), ∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K) := by
  have hle : (P : FractionalIdeal R⁰ K) * I ≤ I := by
    calc (P : FractionalIdeal R⁰ K) * I ≤ 1 * I := by
          gcongr; exact FractionalIdeal.coeIdeal_le_one
      _ = I := one_mul I
  have hne : (P : FractionalIdeal R⁰ K) * I ≠ I := by
    intro h
    have h1 : (P : FractionalIdeal R⁰ K) = 1 := mul_right_cancel₀ hI (by rw [h, one_mul])
    exact hP.ne_top (by simpa using (FractionalIdeal.coeIdeal_eq_one.1 h1))
  obtain ⟨t₀, ht₀, ht₀'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  refine ⟨t₀, ht₀, ?_⟩
  set S : FractionalIdeal R⁰ K := FractionalIdeal.spanSingleton R⁰ t₀ + (P : FractionalIdeal R⁰ K) * I with hS
  have hSle : S ≤ I := by
    rw [hS, ← FractionalIdeal.sup_eq_add]
    exact sup_le (FractionalIdeal.spanSingleton_le_iff_mem.2 ht₀) hle
  have hPS : (P : FractionalIdeal R⁰ K) * I ≤ S := by
    rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
  have hJ : S * I⁻¹ ≤ 1 := by
    calc S * I⁻¹ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  obtain ⟨J, hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ
  have hSJ : S = (J : FractionalIdeal R⁰ K) * I := by
    rw [hJ', mul_assoc, inv_mul_cancel₀ hI, mul_one]
  have hPJ : P ≤ J := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K, hJ']
    calc (P : FractionalIdeal R⁰ K) = (P * I) * I⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ S * I⁻¹ := by gcongr
  have hJt : J = ⊤ := by
    by_contra h
    have hPJ' := hP.eq_of_le h hPJ
    apply ht₀'
    rw [hPJ', ← hSJ]
    have : FractionalIdeal.spanSingleton R⁰ t₀ ≤ S := by
      rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact this (FractionalIdeal.mem_spanSingleton_self _ _)
  have hSI : S = I := by rw [hSJ, hJt, FractionalIdeal.coeIdeal_top, one_mul]
  intro t ht
  have ht' : t ∈ (S : Submodule R K) := by rw [hSI]; exact ht
  rw [hS, FractionalIdeal.coe_add, coe_ideal_mul, FractionalIdeal.coe_spanSingleton, Submodule.add_eq_sup,
    Submodule.mem_sup] at ht'
  obtain ⟨y, hy, z, hz, rfl⟩ := ht'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  exact ⟨a, by simpa using hz⟩

theorem mem_range_of_mul_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (x : K)
    (h : ∀ t ∈ (I : Submodule R K), x * t ∈ (I : Submodule R K)) : x ∈ (algebraMap R K).range := by
  have h1 : FractionalIdeal.spanSingleton R⁰ x * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.2 h
  have h2 : FractionalIdeal.spanSingleton R⁰ x ≤ 1 := by
    calc FractionalIdeal.spanSingleton R⁰ x = (FractionalIdeal.spanSingleton R⁰ x * I) * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  exact (FractionalIdeal.mem_one_iff _).1 (FractionalIdeal.spanSingleton_le_iff_mem.1 h2)

theorem exists_gen_and {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), (∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K)) ∧
      ∀ θ : K, θ ∉ (algebraMap R K).range → (∀ p ∈ P, p • θ ∈ (algebraMap R K).range) →
        ∀ a : R, a • (t₀ * θ) ∈ (I : Submodule R K) → a ∈ P := by
  obtain ⟨t₀, ht₀, hgen⟩ := exists_gen P hP I hI
  refine ⟨t₀, ht₀, hgen, fun θ hθ hPθ a ha => ?_⟩
  by_contra haP
  have hθP : ∀ z ∈ P • (I : Submodule R K), θ * z ∈ (I : Submodule R K) := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun p hp n hn => ?_) (fun x y hx hy => ?_)
    · obtain ⟨q, hq⟩ := hPθ p hp
      have : θ * p • n = q • n := by
        rw [Algebra.smul_def q, hq, smul_mul_assoc, mul_smul_comm]
      rw [this]; exact Submodule.smul_mem _ _ hn
    · rw [mul_add]; exact add_mem hx hy
  have haθ : a • θ ∈ (algebraMap R K).range := by
    refine mem_range_of_mul_mem I hI _ fun t ht => ?_
    obtain ⟨b, hb⟩ := hgen t ht
    have : a • θ * t = a • (θ * (t - b • t₀)) + b • (a • (t₀ * θ)) := by
      simp only [Algebra.smul_def]; ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (hθP _ hb)) (Submodule.smul_mem _ _ ha)
  obtain ⟨u, p, hp, hup⟩ := hP.exists_inv haP
  apply hθ
  have : θ = algebraMap R K u * (a • θ) + p • θ := by
    rw [← Algebra.smul_def, smul_smul, ← add_smul, hup, one_smul]
  rw [this]
  exact add_mem (mul_mem ⟨u, rfl⟩ haθ) (hPθ p hp)

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  unfold Formalism.BasicNotions.Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)

theorem isFractional_Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : IsFractional (𝓞 D.host.E)⁰ (Iid D cc) := by
  obtain ⟨d, hd, hd'⟩ := D.host.AA0.isFractional
  refine (FractionalIdeal.isFractional_span_iff).2 ⟨d, hd, ?_⟩
  rintro _ ⟨c, -, a, ha, rfl⟩
  rw [← mul_smul_comm]
  refine IsLocalization.isInteger_mul ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩ (hd' a ha)

theorem Iid_ne_bot (D : D7) (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) : Iid D cc ≠ ⊥ := by
  obtain ⟨c, hcc, hc0⟩ := (Submodule.ne_bot_iff _).1 hc
  have hA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    inverseHalfDifferent_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 hA
  refine (Submodule.ne_bot_iff _).2 ⟨_, Submodule.subset_span ⟨c, hcc, a, ha, rfl⟩, mul_ne_zero ?_ ha0⟩
  intro h
  apply hc0
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem exists_generator_Iid : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ t₀ ∈ Iid D cc, (∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) ∧ ∀ θ : D.host.E, ¬ IntE D θ → (∀ p ∈ P, IntE D (p • θ)) → ∀ a : 𝓞 D.host.E, a • (t₀ * θ) ∈ Iid D cc → a ∈ P := by
  intro D cc hc P hP
  exact exists_gen_and P hP ⟨Iid D cc, isFractional_Iid D cc⟩
    (fun h => Iid_ne_bot D cc hc (FractionalIdeal.coeToSubmodule_eq_bot.2 h))

end GlobalTheory.IdealGenerator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.FinWeil

noncomputable def ofPrimeValues (u : ℕ → ℂ) : ℕ →* ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun q k => u q ^ k
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Nat.factorization_mul ha hb,
      Finsupp.prod_add_index' (by simp) (fun q k l => pow_add _ _ _)]

theorem ofPrimeValues_prime (u : ℕ → ℂ) {q : ℕ} (hq : q.Prime) : ofPrimeValues u q = u q := by
  show (if q = 0 then 0 else q.factorization.prod fun q k => u q ^ k) = u q
  rw [if_neg hq.ne_zero, hq.factorization, Finsupp.prod_single_index (by simp), pow_one]

theorem sqrt_pow_nat (q f : ℕ) : ((Real.sqrt q : ℝ) : ℂ) ^ f = (Real.sqrt ((q ^ f : ℕ) : ℝ) : ℂ) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [pow_succ, ih, pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

theorem exists_lam (S : ℕ → Prop) (f : ℕ → ℕ) :
    ∃ lam : ℕ →* ℂ, (∀ n, n ≠ 0 → lam n ≠ 0) ∧
      (∀ q, q.Prime → f q ≠ 0 → S q → lam (q ^ f q) = -(Real.sqrt ((q ^ f q : ℕ) : ℝ) : ℂ)) ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → S q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  let u : ℕ → ℂ := fun q =>
    (Real.sqrt q : ℂ) * if S q then Complex.exp (Real.pi * Complex.I / f q) else 1
  refine ⟨ofPrimeValues u, fun n => ?_, fun q hq hf hS => ?_, fun n => ?_⟩
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _
      rw [ofPrimeValues_prime u hq]
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hq.pos)).ne'
      · split_ifs
        · exact Complex.exp_ne_zero _
        · exact one_ne_zero
    | mul a b ha hb =>
      intro h
      rw [map_mul]
      exact mul_ne_zero (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  · rw [map_pow, ofPrimeValues_prime u hq]
    simp only [u, if_pos hS]
    have hf' : (f q : ℂ) ≠ 0 := by exact_mod_cast hf
    rw [mul_pow, sqrt_pow_nat, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hf', Complex.exp_pi_mul_I]
    ring
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _ h
      have hS : ¬ S q := fun hS => h q hq hS dvd_rfl
      rw [ofPrimeValues_prime u hq]
      simp only [u, if_neg hS, mul_one]
    | mul a b ha hb =>
      intro h h'
      rw [map_mul, ha (left_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_right _),
        hb (right_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_left _), Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

theorem exists_card_eq_pow {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ P ∧
      (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) ≠ 0 ∧
      Nat.card (𝓞 E ⧸ P) = q ^ (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) := by
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨p, hp, hPp⟩ :=
    (Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ P)).resolve_left (Ideal.under_ne_bot ℤ hP0)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPp.symm⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have h1 := Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P (E ≃ₐ[ℚ] E)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · have : (p : ℤ) ∈ P.under ℤ := hPp ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this
  · rw [h1]; exact (Ideal.inertiaDeg_pos P ℤ).ne'
  · rw [h1, Ideal.pow_inertiaDeg p P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem exists_goodNorm : ∀ D : D7, ∃ lam : ℕ →* ℂ, GoodNorm (sgO D) lam ∧ ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  intro D
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ := fun σ τ =>
    D.host.galE_injective (by
      rw [D.host.galE_mul,
        D.host.galE_mul, mul_comm])
  obtain ⟨lam, h0, h1, h2⟩ := exists_lam (InertQ D)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 D.host.E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨q, hq, hqP, hf, hc⟩ := exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun h => ⟨?_, ?_⟩⟩
  · rw [hc]
    by_cases hI : InertQ D q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · have hfix : D.host.conj • P = P := by
      have hP' : (D.host.conj • P).IsMaximal := by
        rcases Ideal.map_eq_top_or_isMaximal_of_surjective (sgO D)
          (MulAction.surjective D.host.conj) hP with h | h
        · exact absurd h (Ideal.IsPrime.smul (H := hP.isPrime) D.host.conj).ne_top
        · exact h
      exact hP'.eq_of_le hP.ne_top (Ideal.map_le_iff_le_comap.2 fun r hr => h r hr)
    have hI : InertQ D q := fun Q hQ _ hqQ =>
      GlobalTheory.SelectIdem.smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ hqP hqQ hfix
    rw [hc]
    exact h1 q hq hf hI
  · have := D.host.der.unramEF P hP.isPrime hP0
    push Not at this
    exact this

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.VacMove

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem sgA_sgA (D : D7) (y : AE D) : sgA D (sgA D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sgA_mem (D : D7) {s : AE D} (hs : s ∈ OhE D) : sgA D s ∈ OhE D :=
  Formalism.UG.P.csDual_sig_mem _ hs

theorem inc_int (D : D7) (b : 𝓞 D.host.E) : inc D (b : D.host.E) ∈ OhE D :=
  Formalism.UG.P.adelstab_incl_int (F := ℚ) b

theorem inc_dvd (D : D7) {N : ℕ} {b : 𝓞 D.host.E} (h : (N : 𝓞 D.host.E) ∣ b) :
    ∃ w ∈ OhE D, inc D (b : D.host.E) = (N : AE D) * w := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨_, inc_int D c, ?_⟩
  rw [← map_natCast (inc D), ← map_mul]
  simp

theorem exists_nat_denom (D : D7) (y : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D :=
  (_root_.GlobalTheory.AdelicApprox.approx_mod_ideal D ⊤ top_ne_bot).2.1 y

theorem zeroAt_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ZeroAt D q (x * y) := by
  intro k
  obtain ⟨n, hn, hy⟩ := exists_nat_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx (k + a)
  refine ⟨m * n', Nat.mul_pos hm (Nat.pos_of_ne_zero (by rintro rfl; simp at hn')),
    Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, _, mul_mem hs hy, ?_⟩
  push_cast
  linear_combination (n' : AE D) * y * h

theorem exists_half_idem (D : D7) : ∃ ε ∈ OhE D, ε * ε = ε ∧ ε * sgA D ε = 0 ∧ ∀ q : ℕ, q.Prime →
    (InertQ D q → ZeroAt D q (ε + sgA D ε)) ∧ (¬ InertQ D q → ZeroAt D q (1 - (ε + sgA D ε))) := by
  obtain ⟨e, h1, h2, h3⟩ := _root_.GlobalTheory.SelectIdem.exists_select_idem D
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.T.cmFiniteAdele_integral_separated_complete D
  have hc : ∀ b : 𝓞 D.host.E, inc D ((D.host.conj • b : 𝓞 D.host.E) : D.host.E) = sgA D (inc D b) := by
    intro b
    rw [GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  obtain ⟨ε, hε, h⟩ := hcpl (fun N => inc D (e N : D.host.E)) (fun N => inc_int D _) (by
    intro N m hN hm
    obtain ⟨w, hw, h⟩ := inc_dvd D (h1 N m hN hm)
    refine ⟨w, hw, ?_⟩
    rw [← h]; simp)
  refine ⟨ε, hε, ?_, ?_, fun q hq => ⟨fun hi k => ?_, fun hi k => ?_⟩⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨v, hv, hh'⟩ := inc_dvd D (h2 N hN).1
    have hh'' : inc D (e N : D.host.E) * inc D (e N : D.host.E) - inc D (e N : D.host.E) = N * v := by
      rw [← hh']; simp
    refine ⟨v + (2 * inc D (e N : D.host.E) * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem hv (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (inc_int D _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [hh]; linear_combination hh''
  · refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨v, hv, hh'⟩ := inc_dvd D (h2 N hN).2
    have hh'' : inc D (e N : D.host.E) * sgA D (inc D (e N : D.host.E)) = N * v := by
      rw [← hh', ← hc]; simp
    refine ⟨v + (inc D (e N : D.host.E) * sgA D w + w * sgA D (inc D (e N : D.host.E)) + N * w * sgA D w), ?_, ?_⟩
    · exact add_mem hv (add_mem (add_mem (mul_mem (inc_int D _) (sgA_mem D hw))
        (mul_mem hw (sgA_mem D (inc_int D _)))) (mul_mem (mul_mem (natCast_mem _ _) hw) (sgA_mem D hw)))
    · rw [hh, map_add (f := _), map_mul, map_natCast]; linear_combination hh''
  · obtain ⟨w, hw, hh⟩ := h (q ^ k) (pow_pos hq.pos k)
    obtain ⟨v, hv, hh'⟩ := inc_dvd D ((h3 q k hq).1 hi)
    have hh'' : inc D (e (q ^ k) : D.host.E) + sgA D (inc D (e (q ^ k) : D.host.E)) = (q ^ k : ℕ) * v := by
      rw [← hh', ← hc]; simp
    refine ⟨1, one_pos, by simp, v + (w + sgA D w), add_mem hv (add_mem hw (sgA_mem D hw)), ?_⟩
    rw [hh, map_add (f := _), map_mul, map_natCast]
    push_cast at hh'' ⊢
    linear_combination hh''
  · obtain ⟨w, hw, hh⟩ := h (q ^ k) (pow_pos hq.pos k)
    obtain ⟨v, hv, hh'⟩ := inc_dvd D ((h3 q k hq).2 hi)
    have hh'' : 1 - (inc D (e (q ^ k) : D.host.E) + sgA D (inc D (e (q ^ k) : D.host.E))) = (q ^ k : ℕ) * v := by
      rw [← hh', ← hc]; simp
    refine ⟨1, one_pos, by simp, v - (w + sgA D w), sub_mem hv (add_mem hw (sgA_mem D hw)), ?_⟩
    rw [hh, map_add (f := _), map_mul, map_natCast]
    push_cast at hh'' ⊢
    linear_combination hh''

theorem exists_splitComp (D : D7) (u : (AE D)ˣ) (hu : (u : AE D) * sgA D u = 1) :
    ∃ z x : (AE D)ˣ, SplitComp D u z ∧ x = z * sgU D x ∧ ((u : AE D) ∈ OhE D → IntU D x) := by
  obtain ⟨ε, hε, h1, h2, h3⟩ := exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  set η := sgA D ε with hη
  set v := sgA D u with hv
  have hz : ((1 - (ε + η)) + (ε + η) * u) * ((1 - (ε + η)) + (ε + η) * v) = 1 := by
    linear_combination (1 - u - v + u * v) * (h1 + h1' + 2 * h2) + (ε + η) * hu
  have hx : ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
    linear_combination (1 - u - v + u * v) * h1' + η * hu
  refine ⟨⟨_, _, hz, by rw [mul_comm, hz]⟩, ⟨_, _, hx, by rw [mul_comm, hx]⟩, fun q hq => ⟨fun hi => ?_, fun hi => ?_⟩,
    ?_, fun hO => ⟨?_, ?_⟩⟩
  · convert zeroAt_mul D hq ((h3 q hq).1 hi) (u - 1) using 1
    simp only; ring
  · convert zeroAt_mul D hq ((h3 q hq).2 hi) (1 - u) using 1
    simp only; ring
  · ext
    change (1 - η) + η * u = ((1 - (ε + η)) + (ε + η) * u) * sgA D ((1 - η) + η * u)
    rw [map_add (f := _), map_mul, map_sub, map_one, hη, sgA_sgA, ← hη, ← hv]
    linear_combination (-(1 - u - v + u * v)) * (h1 + h2) - ε * hu
  · exact add_mem (sub_mem (one_mem _) (sgA_mem D hε)) (mul_mem (sgA_mem D hε) hO)
  · exact add_mem (sub_mem (one_mem _) (sgA_mem D hε)) (mul_mem (sgA_mem D hε) (sgA_mem D hO))

theorem det_norm (D : D7) {N : ℕ} (g : GA D N) :
    ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) *
      sgA D ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) = 1 := by
  have h := congrArg Matrix.det ((GlobalTheory.NormSum.PtsMem.mem_GA D _).1 g.2)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, mul_comm]
  exact h

theorem det_int (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) (hg : IntG D g) :
    ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) ∈ OhE D := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => (hg _ _).1)

end GlobalTheory.NormSum.VacMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeTo
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TraceOne

theorem exists_of_sq (D : D7) (q n : ℕ) (hn : n % 4 = 3) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n + 1 = 4 * m := ⟨(n + 1) / 4, by omega⟩
  have hm' : (n : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
  have hint : IsIntegral ℤ ((1 + b) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, map_natCast]
      linear_combination (1 / 4 : D.host.E) * hb - (1 / 4 : D.host.E) * hm'
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  have hcw : D.host.conj ((1 + b) / 2) = (1 - b) / 2 := by
    rw [map_div₀, map_add (f := _), map_one, map_ofNat, hconj, sub_eq_add_neg]
  let w : 𝓞 D.host.E := ⟨(1 + b) / 2, hint⟩
  have hw : (w : D.host.E) = (1 + b) / 2 := rfl
  have hs : ((sgO D w : 𝓞 D.host.E) : D.host.E) = (1 - b) / 2 := by rw [sgO_coe, hw, hcw]
  refine ⟨w, ?_, fun P hP hq hmem => ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_add (f := _), map_one]
    change (w : D.host.E) + ((sgO D w : 𝓞 D.host.E) : D.host.E) = 1
    rw [hw, hs]; ring
  · have hsq : (w - sgO D w) * -(w - sgO D w) = (n : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_neg, map_sub, map_natCast]
      change ((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) *
        -((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) = _
      rw [hw, hs]
      linear_combination (-1 : D.host.E) * hb
    have hnP : (n : 𝓞 D.host.E) ∈ P := hsq ▸ P.mul_mem_right _ hmem
    obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2
      (huv ▸ P.add_mem (P.mul_mem_left u hq) (P.mul_mem_left v hnP)))

theorem exists_trace_one : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  intro D q hq
  obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
  by_cases h : q = D.host.d
  · refine exists_of_sq D q D.host.q (by omega) ((Nat.coprime_primes hq hq₁).2 (by omega))
      (D.host.sqq) D.host.sqq_sq
  · exact exists_of_sq D q D.host.d (by omega) ((Nat.coprime_primes hq hd).2 h)
      (D.host.sqd) (D.host.sqd_sq)

end GlobalTheory.TraceOne
end

