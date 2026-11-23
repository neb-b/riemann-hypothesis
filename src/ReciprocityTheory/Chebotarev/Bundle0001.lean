module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
section
namespace ReciprocityTheory.Cheb

open Polynomial NumberField

private theorem setOf_prime_ramified_finite (K : Type*) [Field K] [NumberField K] :
    {p : ℕ | p.Prime ∧ ∃ (P : Ideal (𝓞 K)) (_ : P.IsPrime), (p : 𝓞 K) ∈ P ∧
      ¬ Algebra.IsUnramifiedAt ℤ P}.Finite := by
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hF := Ideal.finite_factors (I := differentIdeal ℤ (𝓞 K)) (by simpa using hD)

  have hsub : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      {p : ℕ | p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal}.Subsingleton := by
    intro v p ⟨hp, hpv⟩ q ⟨hq, hqv⟩
    by_contra hne
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
    have hc : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := by
      have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 K))
      simpa using this
    obtain ⟨a, b, hab⟩ := hc
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := hab ▸
      v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  refine (hF.biUnion (fun v _ => (hsub v).finite)).subset ?_
  rintro p ⟨hp, P, hPp, hpP, hnr⟩
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  exact Set.mem_biUnion (x := ⟨P, hPp, hP0⟩) (dvd_differentIdeal_iff.mpr hnr) ⟨hp, hpP⟩

theorem exists_forall_isUnramifiedAt (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N < p → ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (p : 𝓞 K) ∈ P →
      Algebra.IsUnramifiedAt ℤ P := by
  obtain ⟨N, hN⟩ := (setOf_prime_ramified_finite K).bddAbove
  refine ⟨N, fun p hp hpN P _ hpP => ?_⟩
  by_contra h
  exact absurd (hN ⟨hp, P, inferInstance, hpP, h⟩) (not_le.mpr hpN)

theorem natCast_notMem_sq_of_isUnramifiedAt {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [Algebra.IsUnramifiedAt ℤ P] : (l : 𝓞 K) ∉ P ^ 2 := by
  intro hl2
  have hlP : (l : 𝓞 K) ∈ P := Ideal.pow_le_self two_ne_zero hl2
  have hl0 : (l : 𝓞 K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hlP
    exact hl0 hlP
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {(l : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.under, Ideal.mem_comap] using hlP
  have hunder : Ideal.span {(l : ℤ)} = P.under ℤ :=
    hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top hle
  haveI : P.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hunder⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  have hcount := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(l : ℤ)}) P hmap0
  rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcount

  have hdvd : P ^ 2 ∣ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) := by
    rw [Ideal.dvd_iff_le, hmap, Ideal.span_le, Set.singleton_subset_iff]
    exact hl2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hP0)
  have hnf := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP2
    (by simpa using hmap0)).mp hdvd
  have hc := Multiset.count_le_of_le P hnf
  rw [← hcount, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 inferInstance).irreducible,
    normalize_eq] at hc
  simp at hc

theorem cyclotomic_irreducible_of_isUnramifiedAt {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime] (hlP : (l : 𝓞 K) ∈ P)
    [Algebra.IsUnramifiedAt ℤ P] : Irreducible (cyclotomic l K) := by
  haveI := Fact.mk hl
  have hl2 := natCast_notMem_sq_of_isUnramifiedAt hl P

  have hE := cyclotomic_comp_X_add_one_isEisensteinAt l
  have hX1 : (X + 1 : ℤ[X]).Monic := by simpa using monic_X_add_C (1 : ℤ)
  have hX1d : (X + 1 : ℤ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℤ)
  have hmon : ((cyclotomic l ℤ).comp (X + 1)).Monic :=
    (cyclotomic.monic l ℤ).comp hX1 (by rw [hX1d]; exact one_ne_zero)
  have hg : ((cyclotomic l ℤ).comp (X + 1)).map (Int.castRingHom (𝓞 K)) = (cyclotomic l (𝓞 K)).comp (X + 1) := by
    simp [Polynomial.map_comp, map_cyclotomic]
  have hdeg : (((cyclotomic l ℤ).comp (X + 1)).map (Int.castRingHom (𝓞 K))).natDegree =
      ((cyclotomic l ℤ).comp (X + 1)).natDegree := hmon.natDegree_map _
  have hc0 : ((cyclotomic l ℤ).comp (X + 1)).coeff 0 = l := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp [eval_one_cyclotomic_prime]
  have hE' : ((cyclotomic l (𝓞 K)).comp (X + 1)).IsEisensteinAt P := by
    rw [← hg]
    refine ⟨?_, ?_, ?_⟩
    · rw [(hmon.map _).leadingCoeff]
      exact (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance)
    · intro n hn
      rw [hdeg] at hn
      rw [coeff_map]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hE.mem hn)
      rw [← hc, smul_eq_mul, map_mul, map_natCast]
      exact P.mul_mem_left _ hlP
    · rw [coeff_map, hc0, map_natCast]
      exact hl2
  have hpos : 0 < ((cyclotomic l (𝓞 K)).comp (X + 1)).natDegree := by
    rw [← hg, hdeg, natDegree_comp, natDegree_cyclotomic, hX1d, mul_one, Nat.totient_prime hl]
    exact Nat.sub_pos_of_lt hl.one_lt
  have hmon' : ((cyclotomic l (𝓞 K)).comp (X + 1)).Monic := by
    rw [← hg]
    exact hmon.map _
  have hirr1 := hE'.irreducible inferInstance hmon'.isPrimitive hpos
  have hcomp : (algEquivAevalXAddC (1 : 𝓞 K)) (cyclotomic l (𝓞 K)) = (cyclotomic l (𝓞 K)).comp (X + 1) := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval, map_one]
  have hirr2 : Irreducible (cyclotomic l (𝓞 K)) := by
    rw [← hcomp] at hirr1
    exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : 𝓞 K)).toMulEquiv).mp hirr1
  have := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := K)
    (cyclotomic.monic l (𝓞 K))).mp hirr2
  rwa [map_cyclotomic] at this

theorem cyclotomic_irreducible_of_forall_isUnramifiedAt {K : Type*} [Field K] [NumberField K]
    {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (l : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt ℤ P) :
    Irreducible (cyclotomic l K) := by
  have hnu : ¬ IsUnit (l : 𝓞 K) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [show (l : 𝓞 K) = algebraMap ℤ (𝓞 K) (l : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h1
    simp at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := Ideal.exists_le_maximal (Ideal.span {(l : 𝓞 K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hlM' : (l : 𝓞 K) ∈ M := hlM (Ideal.mem_span_singleton_self _)
  haveI := h M hlM'
  exact cyclotomic_irreducible_of_isUnramifiedAt hl M hlM'

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.EulerSum
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

noncomputable def idealZetaR (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)

theorem idealZetaR_tendsto_sum_card_div (E : Type) [Field E] [NumberField E] :
    ∃ c : ℝ, Tendsto (fun n : ℕ ↦
    (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ)) / n)
      atTop (𝓝 c) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ E).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem idealZetaR_term_eq (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 0 < s) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n =
      (((Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  · rw [LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n), div_eq_mul_inv]
    push_cast
    rfl

theorem summable_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  obtain ⟨c, hc⟩ := idealZetaR_tendsto_sum_card_div E
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    simp_rw [Real.rpow_one]
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c hc
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd h (Nat.cast_ne_zero.mpr hn)
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (s := (s : ℂ)) (by simpa using hs)
  unfold LSeriesSummable at this
  have h2 := (funext (idealZetaR_term_eq E (zero_lt_one.trans hs)))
  simp only [Complex.ofReal_natCast] at this h2
  rw [h2] at this
  exact Complex.summable_ofReal.mp this

theorem dedekindZeta_eq_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E (s : ℂ) = ((idealZetaR E s : ℝ) : ℂ) := by
  unfold dedekindZeta LSeries idealZetaR
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ idealZetaR_term_eq E (zero_lt_one.trans hs) n

theorem sum_le_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s)
    (T : Finset (Ideal (𝓞 E))) :
    ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤ idealZetaR E s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Ideal.absNorm) (t := T.image Ideal.absNorm)
    (fun I hI ↦ Finset.mem_image_of_mem _ hI)]
  refine le_trans ?_ ((summable_idealZetaR E hs).sum_le_tsum (T.image Ideal.absNorm)
    (fun n _ ↦ by positivity))
  refine Finset.sum_le_sum fun n _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ (n : ℝ) ^ (-s))
    (fun I hI ↦ by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const, nsmul_eq_mul]
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n
  have hc : Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} = hfin.toFinset.card :=
    Nat.card_eq_card_finite_toFinset hfin
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [hc, Nat.cast_le]
  refine Finset.card_le_card fun I hI ↦ ?_
  simp only [Finset.mem_filter] at hI
  simpa using hI.2

theorem summable_absNorm_rpow_ideal (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) :=
  summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ sum_le_idealZetaR E hs u

end ReciprocityTheory.Cheb
end

