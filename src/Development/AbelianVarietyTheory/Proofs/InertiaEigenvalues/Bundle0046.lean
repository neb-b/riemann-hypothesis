module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRootEqOne
section
namespace GlobalTheory.RootValuationOne

open Finset

theorem sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x y : Ω}
    (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1) (hd : A.valuation (x - y) < 1) (i : ℕ) :
    A.valuation (x ^ i - y ^ i) < 1 := by
  rw [← geom_sum₂_mul, map_mul]
  have hs : A.valuation (∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro j _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _)
  calc _ ≤ 1 * A.valuation (x - y) := by gcongr
    _ < 1 := by rw [one_mul]; exact hd

theorem val_root_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {x : Ω} (hx : x ^ n = 1) : A.valuation x = 1 := by
  have h : A.valuation x ^ n = 1 := by rw [← map_pow, hx, map_one]
  rcases lt_trichotomy (A.valuation x) 1 with h' | h' | h'
  · exact absurd h (pow_lt_one₀ zero_le' h' hn0).ne
  · exact h'
  · exact absurd h (one_lt_pow₀ h' hn0).ne'

theorem main : ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) (n : ℕ),
    ¬(ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (↑n : Ω) < (1 : ValuationSubring.ValueGroup A) →
    ∀ {ξ ξ' : Ω}, ξ ^ n = (1 : Ω) → ξ' ^ n = (1 : Ω) →
    (ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (ξ - ξ') < (1 : ValuationSubring.ValueGroup A) → ξ = ξ' := by
  intro Ω _ A n hn ξ ξ' h1 h2 hd
  have hn0 : n ≠ 0 := by rintro rfl; apply hn; simp
  have hv1 := val_root_eq_one A hn0 h1
  have hv2 := val_root_eq_one A hn0 h2
  by_contra hne
  have hs : ∑ i ∈ range n, ξ ^ i * ξ' ^ (n - 1 - i) = 0 := by
    have := geom_sum₂_mul ξ ξ' n
    rw [h1, h2, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt : A.valuation (∑ i ∈ range n, (ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1))) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    have hi' : i + (n - 1 - i) = n - 1 := by
      have := mem_range.mp hi; omega
    have e : ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1) = (ξ ^ i - ξ' ^ i) * ξ' ^ (n - 1 - i) := by
      rw [sub_mul, ← pow_add, hi']
    rw [e, map_mul, map_pow, hv2, one_pow, mul_one]
    exact sub_pow_lt_one A hv1.le hv2.le hd i
  rw [sum_sub_distrib, hs, sum_const, card_range, zero_sub, Valuation.map_neg, nsmul_eq_mul,
    map_mul, map_pow, hv2, one_pow, mul_one] at hlt
  exact hn hlt

end GlobalTheory.RootValuationOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEmbeddingGeneratorEqOne
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem ringOfIntegers_map_mem_valuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) (x : 𝓞 K) : σ (x : K) ∈ A := by
  have h1 : IsIntegral ℤ (σ (x : K)) := (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (x : K)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

noncomputable def ringOfIntegersToValuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) : 𝓞 K →+* A :=
  ((σ.comp (algebraMap (𝓞 K) K)).codRestrict A.toSubring
    (fun x => ringOfIntegers_map_mem_valuationSubring A σ x))

theorem valuation_embedding_generator_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
      ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h →
      ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by
  intro K _ _ A p _ hpA P hpP α h hα σ
  set f := ringOfIntegersToValuationSubring A σ with hf
  have hfx : ∀ x : 𝓞 K, ((f x : A) : ℂ) = σ (x : K) := fun x => rfl
  set Q : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime f (IsLocalRing.maximalIdeal A)
  have hQne : Q ≠ ⊤ := hQp.ne_top
  have hmem : ∀ x : 𝓞 K, x ∈ Q ↔ A.valuation (σ (x : K)) < 1 := by
    intro x
    rw [hQ, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hfx]
  have hpQ : (p : 𝓞 K) ∈ Q := by
    rw [hmem]
    have : σ (((p : 𝓞 K) : K)) = (p : ℂ) := by simp
    rw [this]
    exact (ValuationSubring.mem_nonunits_iff A).mp hpA
  refine le_antisymm ?_ ?_
  · exact (ValuationSubring.valuation_le_one_iff A _).mpr (ringOfIntegers_map_mem_valuationSubring A σ α)
  · by_contra hlt
    push_neg at hlt
    have hαQ : α ∈ Q := (hmem α).mpr hlt
    have hspan : P.asIdeal ^ h ≤ Q := by
      rw [← hα, Ideal.span_singleton_le_iff_mem]
      exact hαQ
    have hPQ : P.asIdeal ≤ Q := Ideal.IsPrime.le_of_pow_le hspan
    have hPeq : P.asIdeal = Q := P.isMaximal.eq_of_le hQne hPQ
    exact hpP (hPeq ▸ hpQ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLeOneOfSqSubSelfIntegralBasis
section
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem integral_of_sq_sub_integral (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (hbi : ∀ i, IsIntegral ℤ (b i))
    (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E'))
    (hw : w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal) (ε : E')
    (hε : ∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) : w''.valuation E' ε ≤ 1 := by
  have hunder : w''.under (𝓞 E) = w := HeightOneSpectrum.ext hw
  have hc : ∀ c : E, w.valuation E c ≤ 1 → w''.valuation E' (algebraMap E E' c) ≤ 1 := by
    intro c hc
    subst hunder
    have : w''.asIdeal.LiesOver (w''.under (𝓞 E)).asIdeal := ⟨rfl⟩
    rw [← HeightOneSpectrum.valuation_liesOver E' (w''.under (𝓞 E)) w'' c]
    exact pow_le_one' hc _
  have hb : ∀ i, w''.valuation E' (b i) ≤ 1 := by
    intro i
    have : b i = algebraMap (𝓞 E') E' (⟨b i, (mem_integralClosure_iff ℤ E').2 (hbi i)⟩ : 𝓞 E') := rfl
    rw [this]
    exact w''.valuation_le_one _
  have hu : w''.valuation E' (ε * ε - ε) ≤ 1 := by
    rw [← b.sum_repr (ε * ε - ε)]
    refine (Valuation.map_sum_le _ fun i _ => ?_)
    rw [Algebra.smul_def, map_mul]
    exact mul_le_one' (hc _ (hε i)) (hb i)
  by_contra h
  push_neg at h
  have h2 : w''.valuation E' (ε * ε) ≤ w''.valuation E' ε := by
    have : ε * ε = ε + (ε * ε - ε) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le le_rfl (hu.trans h.le))
  rw [map_mul] at h2
  have h0 : (0 : _) < w''.valuation E' ε := lt_trans zero_lt_one h
  have := mul_lt_mul_of_pos_left h h0
  rw [mul_one] at this
  exact absurd h2 (not_le.2 this)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
section
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_not_mem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [valuation_of_mk'] at ht
  set n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hn
  have hvb : v.intValuation b = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hb0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < v.intValuation b := by
    rw [hvb]; exact WithZero.exp_pos
  have hva : v.intValuation a ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hvb]; exact (div_le_one₀ hpos).1 ht
  have haI : a ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem a n).1 hva
  have hbI : b ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem b n).1 hvb.le
  have hbI' : b ∉ v.asIdeal ^ (n + 1) := by
    intro h
    have := (v.intValuation_le_pow_iff_mem b (n + 1)).2 h
    rw [hvb] at this
    have h2 := WithZero.exp_le_exp.1 this
    push_cast at h2
    omega
  have hdvd : v.asIdeal ^ n ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbI)
  obtain ⟨B', hB'⟩ := hdvd
  have hB'p : ¬ B' ≤ v.asIdeal := by
    intro hle
    apply hbI'
    have : Ideal.span {b} ≤ v.asIdeal ^ (n + 1) := by
      rw [hB', pow_succ]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self b)
  obtain ⟨s, hsB, hsp⟩ := Set.not_subset.1 hB'p
  refine ⟨s, hsp, ?_⟩
  have hmem : a * s ∈ Ideal.span {b} := by
    rw [hB']; exact Ideal.mul_mem_mul haI hsB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨r, ?_⟩
  show algebraMap R K s * IsLocalization.mk' K a ⟨b, hb⟩ = algebraMap R K r
  rw [IsFractionRing.mk'_eq_div]
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K), (IsFractionRing.injective R K).eq_iff]; exact hb0
  rw [mul_div_assoc', div_eq_iff hbK, ← map_mul, ← map_mul, hr, mul_comm a s]

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal

theorem mul_mem_of_trace_mem {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : L)
    (hx : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range) :
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∃ c : 𝓞 L, (c : L) = x * (d : L) := by
  intro d hd
  have hxd : x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx b
  have hdd : (d : L) ∈ ((differentIdeal (𝓞 K) (𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal (𝓞 K) K] at hdd
  have hm := FractionalIdeal.mul_mem_mul hxd hdd
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero (𝓞 K) K (by simp))] at hm
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  exact ⟨c, hc⟩

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_approx_idempotent {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    ∃ z : 𝓞 L, z ∉ la.asIdeal ∧ ∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la →
      la'.asIdeal.under (𝓞 K) = p.asIdeal → z ∈ la'.asIdeal ^ N := by
  set S : Set (HeightOneSpectrum (𝓞 L)) := {la' | la' ≠ la ∧ la'.asIdeal.under (𝓞 K) = p.asIdeal}
  haveI := p.isMaximal
  have hfin : S.Finite := by
    refine ((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L)).preimage
      (f := HeightOneSpectrum.asIdeal) ?_).subset ?_
    · intro a _ b _ h; exact HeightOneSpectrum.ext h
    · intro la' h
      exact ⟨la'.isPrime, ⟨h.2.symm⟩⟩
  haveI := la.isPrime
  have hw : ∀ la' ∈ S, ∃ w : 𝓞 L, w ∈ la'.asIdeal ^ N ∧ w ∉ la.asIdeal := by
    intro la' h
    by_contra hc
    push_neg at hc
    have h1 : la'.asIdeal ^ N ≤ la.asIdeal := fun w hw => hc w hw
    have h2 := Ideal.IsPrime.le_of_pow_le h1
    exact h.1 (HeightOneSpectrum.ext (la'.isMaximal.eq_of_le la.isPrime.ne_top h2))
  choose! w hwN hwla using hw
  refine ⟨∏ la' ∈ hfin.toFinset, w la', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, hi, hmem⟩
    exact hwla i (hfin.mem_toFinset.1 hi) hmem
  · intro la' h1 h2
    have hS : la' ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨h1, h2⟩
    rw [← Finset.mul_prod_erase _ _ hS]
    exact Ideal.mul_mem_right _ _ (hwN la' ⟨h1, h2⟩)

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem valuation_mul_different_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)),
    la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L,
      (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal →
        b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) →
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  intro K L _ _ _ _ _ la p hp y ⟨N, hN⟩ d hd
  obtain ⟨z, hzla, hzN⟩ := exists_approx_idempotent (K := K) la p N
  set x : L := (z : L) * y with hxdef
  have hx : ∀ b : 𝓞 L, p.valuation K (Algebra.trace K L ((b : L) * x)) ≤ 1 := by
    intro b
    have h := hN (b * z) (fun la' h1 h2 => Ideal.mul_mem_left _ _ (hzN la' h1 h2))
    rw [hxdef, ← mul_assoc]
    simpa using h
  set bs := RingOfIntegers.basis L
  have hloc : ∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K s * Algebra.trace K L ((bs i : L) * x) = algebraMap (𝓞 K) K r :=
    fun i => exists_not_mem_mul_mem p _ (hx (bs i))
  choose s hsp r hr using hloc
  set s0 : 𝓞 K := ∏ i, s i with hs0
  haveI := p.isPrime
  have hs0p : s0 ∉ p.asIdeal := by
    rw [hs0, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, _, hi⟩
    exact hsp i hi
  have hgen : ∀ b : 𝓞 L,
      algebraMap (𝓞 K) K s0 * Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have hb : b ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      rw [hs0, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap _ _ (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => simp
    | add b c _ _ hb hc =>
      have : ((b + c : 𝓞 L) : L) * x = (b : L) * x + (c : L) * x := by push_cast; ring
      rw [this, map_add (f := _), mul_add]
      exact add_mem hb hc
    | smul n b _ hb =>
      have : ((n • b : 𝓞 L) : L) * x = n • ((b : L) * x) := by
        rw [← smul_mul_assoc]; congr 1
      rw [this, map_zsmul, mul_smul_comm]
      exact zsmul_mem hb n
  set x' : L := algebraMap (𝓞 K) L s0 * x with hx'def
  have htr : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x') ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have : (b : L) * x' = (algebraMap (𝓞 K) K s0) • ((b : L) * x) := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, hx'def]; ring
    rw [this, map_smul, smul_eq_mul]
    exact hgen b
  obtain ⟨c, hc⟩ := mul_mem_of_trace_mem x' htr d hd
  have hcle : la.valuation L (c : L) ≤ 1 := la.valuation_le_one c
  have hs0la : la.valuation L (algebraMap (𝓞 K) L s0) = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    refine le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hs0p ?_)
    rw [la.valuation_lt_one_iff_mem] at h
    rw [← hp]
    exact h
  have hzla' : la.valuation L (z : L) = 1 := by
    refine le_antisymm (la.valuation_le_one z) (not_lt.1 fun h => hzla ?_)
    exact (la.valuation_lt_one_iff_mem z).1 h
  have : (c : L) = (algebraMap (𝓞 K) L s0 * (z : L)) * (y * (d : L)) := by
    rw [hc, hx'def, hxdef]; ring
  rw [this, map_mul, map_mul, hs0la, hzla', one_mul, one_mul] at hcle
  exact hcle

end GlobalTheory.InvDiffLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationSqrtAbsNormEqOne
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem valuation_sqrt_absNorm_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
        A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
  intro K _ _ A p hp hpA P hpP
  set N : ℕ := Ideal.absNorm P.asIdeal with hNdef

  have hNcard : N = Nat.card (𝓞 K ⧸ P.asIdeal) := by
    rw [hNdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have hpN : ¬ p ∣ N := by
    intro hdvd
    haveI : Finite (𝓞 K ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hNcard ▸ hN0)
    haveI : Fact p.Prime := ⟨hp⟩
    letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) p (hNcard ▸ hdvd)
    have hx0 : x ≠ 0 := by
      rintro rfl; rw [addOrderOf_zero] at hx; exact hp.one_lt.ne' hx.symm
    have hpx : (p : 𝓞 K ⧸ P.asIdeal) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hp0 : (p : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.mp hpx).resolve_right hx0
    apply hpP
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hp0
  have hcop : Nat.Coprime N p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN))

  have hbez : (N : ℤ) * Nat.gcdA N p + (p : ℤ) * Nat.gcdB N p = 1 := by
    have := Nat.gcd_eq_gcd_ab N p
    rw [hcop] at this; simpa using this.symm
  have hbezA : ((N : A) * ((Nat.gcdA N p : ℤ) : A)) + ((p : A) * ((Nat.gcdB N p : ℤ) : A)) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hbez
    push_cast at this; exact this
  have hpnu : ¬ IsUnit (p : A) := by
    rw [ValuationSubring.valuation_eq_one_iff]
    have := (ValuationSubring.mem_nonunits_iff A).mp hpA
    push_cast; exact this.ne
  have hNu : IsUnit (N : A) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hbezA with h | h
    · exact isUnit_of_mul_isUnit_left h
    · exact absurd (isUnit_of_mul_isUnit_left h) hpnu
  have hvN : A.valuation (N : ℂ) = 1 := by
    have := (ValuationSubring.valuation_eq_one_iff A _).mp hNu
    push_cast at this; exact this

  have hsq : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h2 : A.valuation ((Real.sqrt N : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← map_pow, hsq, hvN]
  rcases lt_trichotomy (A.valuation ((Real.sqrt N : ℝ) : ℂ)) 1 with h | h | h
  · exact absurd h2 (pow_lt_one₀ zero_le' h two_ne_zero).ne
  · exact h
  · exact absurd h2 (one_lt_pow₀ h two_ne_zero).ne'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAroundLastMaxNullSequence
section
open Polynomial

namespace GlobalTheory

theorem window_around_last_max : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  intro β c h hc hβ0 hne hlim
  have hfin : ∀ ε : ℝ, 0 < ε → {k | ε ≤ β k}.Finite := by
    intro ε hε
    have h1 : ∀ᶠ k in Filter.cofinite, β k < ε := hlim.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at h1
    simpa [not_lt] using h1
  obtain ⟨k₀, hk₀⟩ := hne
  have hpos : 0 < β k₀ := lt_of_le_of_ne (hβ0 k₀) (Ne.symm hk₀)
  set T := (hfin _ hpos).toFinset with hT
  have hk₀T : k₀ ∈ T := by simp [T]
  obtain ⟨m, hmT, hm⟩ := T.exists_max_image β ⟨k₀, hk₀T⟩
  have hmax : ∀ k, β k ≤ β m := by
    intro k
    by_cases hk : β k₀ ≤ β k
    · exact hm k (by simp [T, hk])
    · push_neg at hk
      have : β k₀ ≤ β m := hm k₀ hk₀T
      linarith
  set U := T.filter (fun k => β k = β m) with hU
  have hmU : m ∈ U := Finset.mem_filter.2 ⟨hmT, rfl⟩
  set N := U.max' ⟨m, hmU⟩ with hNdef
  have hNU : N ∈ U := U.max'_mem _
  have hN : β N = β m := (Finset.mem_filter.1 hNU).2
  have hk₀m : β k₀ ≤ β m := hm k₀ hk₀T
  have hNlast : ∀ k, N < k → β k < β N := by
    intro k hk
    rcases lt_or_eq_of_le (hmax k) with h1 | h1
    · rw [hN]; exact h1
    · exfalso
      have hkU : k ∈ U := by
        refine Finset.mem_filter.2 ⟨?_, h1⟩
        simp [T]; linarith
      have := U.le_max' k hkU
      omega
  have hc₀ : 0 < β N := by rw [hN]; linarith
  have hcpos : 0 < c * β N := mul_pos hc hc₀
  set F := (hfin _ hcpos).toFinset with hF
  set B : ℕ := (F.image (fun k => k.natAbs)).sup id ⊔ N.natAbs with hB
  have hNB : N.natAbs ≤ B := le_sup_right
  have hFB : ∀ k, c * β N ≤ β k → k.natAbs ≤ B := by
    intro k hk
    have hkF : k ∈ F := by simp [F, hk]
    have : k.natAbs ≤ (F.image (fun k => k.natAbs)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hkF)
    exact le_trans this le_sup_left
  refine ⟨B + h, B + h + B, (N + B).toNat, ?_⟩
  have hx : ((((N + (B : ℤ)).toNat + h : ℕ)) : ℤ) - ((B + h : ℕ) : ℤ) = N := by omega
  rw [hx]
  refine ⟨by omega, by omega, hc₀, fun k => hN ▸ hmax k, fun k hk => hNlast k hk, ?_⟩
  intro k hk
  by_contra hlt
  push_neg at hlt
  have := hFB k hlt.le
  omega

end GlobalTheory
end

