module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplDvr
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.dvr :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (π : R), Prime π →
      ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R (Ideal.span {π}) B →
      ∃ _ : IsDomain B, IsDiscreteValuationRing B ∧ Irreducible (algebraMap R B π) := by
  intro R _ _ _ π hπ B _ _ _ h
  haveI : IsNoetherianRing B := h.noeth
  set f := algebraMap R B with hf
  have hm : maximalIdeal B = Ideal.span {f π} := by
    have h1 := UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq R _ B h 1
    simpa [Ideal.map_span] using h1.symm
  have hpow : ∀ n : ℕ, maximalIdeal B ^ n = Ideal.span {f π ^ n} := by
    intro n
    rw [hm, Ideal.span_singleton_pow]
  have hnil : ∀ n : ℕ, f π ^ n ≠ 0 := by
    intro n hn
    have hmem : f (π ^ n) ∈ maximalIdeal B ^ (n + 1) := by
      rw [map_pow, hn]
      exact zero_mem _
    obtain ⟨s, hs, hs'⟩ := h.strict (n + 1) (π ^ n) hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hs'
    obtain ⟨t, ht⟩ := hs'
    apply hs
    rw [Ideal.mem_span_singleton]
    refine ⟨t, ?_⟩
    have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ.ne_zero
    apply mul_right_cancel₀ hπn
    rw [ht]
    ring
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (Ideal.IsMaximal.ne_top inferInstance)
  have hfac : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : B), IsUnit u ∧ x = f π ^ k * u := by
    intro x hx
    classical
    have hex : ∃ n : ℕ, x ∉ maximalIdeal B ^ n := by
      by_contra hc
      push_neg at hc
      apply hx
      have hin : x ∈ ⨅ i : ℕ, maximalIdeal B ^ i := Submodule.mem_iInf _ |>.mpr hc
      rw [hK] at hin
      exact (Submodule.mem_bot _).mp hin
    have hn : x ∉ maximalIdeal B ^ Nat.find hex := Nat.find_spec hex
    have n0 : Nat.find hex ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hxk : x ∈ maximalIdeal B ^ k := by
      by_contra hc
      have := Nat.find_min' hex hc
      omega
    rw [hpow, Ideal.mem_span_singleton'] at hxk
    obtain ⟨u, rfl⟩ := hxk
    refine ⟨k, u, ?_, by ring⟩
    by_contra hu
    apply hn
    have hum : u ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal u).mpr hu
    rw [hm, Ideal.mem_span_singleton'] at hum
    obtain ⟨c, rfl⟩ := hum
    rw [hk, hpow, Ideal.mem_span_singleton']
    exact ⟨c, by ring⟩
  haveI : IsDomain B := by
    have hnzd : NoZeroDivisors B := ⟨fun {a b} hab => by
      by_contra hc
      push_neg at hc
      obtain ⟨i, u, hu, rfl⟩ := hfac a hc.1
      obtain ⟨j, v, hv, rfl⟩ := hfac b hc.2
      apply hnil (i + j)
      have hz : f π ^ (i + j) * (u * v) = 0 := by
        rw [← hab]
        ring
      exact (hu.mul hv).mul_left_eq_zero.mp hz⟩
    exact NoZeroDivisors.to_isDomain B
  have hirr : Irreducible (f π) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (f π) (by simpa using hnil 1) hm
  refine ⟨inferInstance, ?_, hirr⟩
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨f π, hirr, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := hfac x hx
  exact ⟨n, hu.unit, by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplQuot
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem prec_of_surj {B C : Type} [CommRing B] [CommRing C] (g : B →+* C)
    (I : Ideal B) [hB : IsPrecomplete I B] (hg : Function.Surjective g) :
    IsPrecomplete (I.map g) C := by
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  have h1 : ∀ n, ∃ d ∈ I ^ n, g d = f (n + 1) - f n := by
    intro n
    have := (((I.map g) ^ n).neg_mem (hf (Nat.le_succ n)))
    rw [neg_sub, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective g hg] at this
    exact this
  choose d hd hgd using h1
  obtain ⟨b0, hb0⟩ := hg (f 0)
  let u : ℕ → B := fun n => b0 + ∑ i ∈ Finset.range n, d i
  have hu : ∀ n, g (u n) = f n := by
    intro n
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, map_add (f := _), map_sum, hgd, hb0, Finset.sum_range_sub]
    ring
  have hc : ∀ {m n}, m ≤ n → u m ≡ u n [SMOD (I ^ m • ⊤ : Submodule B B)] := by
    intro m n hmn
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have e : u m - u (k + 1) = (u m - u k) - d k := by
        simp only [u, Finset.sum_range_succ]; ring
      rw [e]
      exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hk (hd k))
  obtain ⟨L, hL⟩ := hB.prec hc
  refine ⟨g L, fun n => ?_⟩
  have := hL n
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← hu, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ this

private theorem approx_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (I : Ideal R) (n : ℕ) (x : B)
    (hx : x ∈ I.map (algebraMap R B)) :
    ∃ i ∈ I, ∃ s : R, s ∉ p ∧ algebraMap R B s * x - algebraMap R B i ∈ maximalIdeal B ^ n := by
  have hp := h.isPrime
  have h1 : (1 : R) ∉ p := (Ideal.ne_top_iff_one _).1 hp.ne_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, 1, h1, by simp⟩
  | zero => exact ⟨0, I.zero_mem, 1, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨j, hj, t, ht, hy⟩ := hy
    refine ⟨t * i + s * j, I.add_mem (I.mul_mem_left _ hi) (I.mul_mem_left _ hj), s * t,
      fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t) hx)
      (Ideal.mul_mem_left _ (algebraMap R B s) hy)
    convert this using 1
    simp only [map_add (f := _), map_mul]; ring
  | smul b x _ hx =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨a, t, ht, hb⟩ := h.dense n b
    refine ⟨a * i, I.mul_mem_left _ hi, s * t, fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t * b) hx)
      (Ideal.mul_mem_left _ (algebraMap R B i) hb)
    convert this using 1
    simp only [map_mul, smul_eq_mul]; ring

theorem UpperTheory.V.AlgebraTools.IsCplAt.quotient :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (S : Type) [CommRing S] [Algebra R S] (q : Ideal S) (C : Type) [CommRing C] [IsLocalRing C]
      [Algebra S C] [Algebra B C] [Algebra R C] [IsScalarTower R S C] [IsScalarTower R B C],
      IsCplAt R p B → Function.Surjective (algebraMap R S) → q.comap (algebraMap R S) = p →
      Function.Surjective (algebraMap B C) →
      RingHom.ker (algebraMap B C) = (RingHom.ker (algebraMap R S)).map (algebraMap R B) → IsCplAt S q C := by
  intro R _ _ p B _ _ _ S _ _ q C _ _ _ _ _ _ _ h hRS hq hBC hker
  haveI := h.noeth
  haveI := h.complete
  have hp := h.isPrime
  have hN : IsNoetherianRing C := isNoetherianRing_of_surjective B C (algebraMap B C) hBC
  haveI hloc : IsLocalHom (algebraMap B C) := IsLocalHom.of_surjective _ hBC
  have hm : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hBC
  have hsq : ∀ r : R, algebraMap S C (algebraMap R S r) = algebraMap B C (algebraMap R B r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hqp : ∀ r : R, algebraMap R S r ∈ q ↔ r ∈ p := by
    intro r; rw [← hq, Ideal.mem_comap]
  have hpre : IsPrecomplete (maximalIdeal C) C := hm ▸ prec_of_surj (algebraMap B C) _ hBC
  refine ⟨hN, {}, ?_, ?_, ?_⟩
  · ext x
    obtain ⟨r, rfl⟩ := hRS x
    rw [hqp, ← h.comap_eq, Ideal.mem_comap, Ideal.mem_comap, hsq, mem_maximalIdeal,
      mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
  · intro n c
    obtain ⟨b, rfl⟩ := hBC c
    obtain ⟨a, s, hs, hab⟩ := h.dense n b
    refine ⟨algebraMap R S a, algebraMap R S s, fun hh => hs ((hqp s).1 hh), ?_⟩
    rw [hsq, hsq, ← map_mul, ← map_sub, ← hm, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hab
  · intro n x hx
    obtain ⟨a, rfl⟩ := hRS x
    rw [hsq, ← hm, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hBC] at hx
    obtain ⟨y, hy, hya⟩ := hx
    have hk : algebraMap R B a - y ∈ RingHom.ker (algebraMap B C) := by
      rw [RingHom.mem_ker, map_sub, hya, sub_self]
    rw [hker] at hk
    obtain ⟨i, hi, s, hs, hsi⟩ := approx_map h _ n _ hk
    have h2 : algebraMap R B (s * a - i) ∈ maximalIdeal B ^ n := by
      have := Ideal.add_mem _ hsi (Ideal.mul_mem_left _ (algebraMap R B s) hy)
      convert this using 1
      simp only [map_sub, map_mul]; ring
    obtain ⟨t, ht, hta⟩ := h.strict n _ h2
    refine ⟨algebraMap R S (t * s), fun hh => (hp.mem_or_mem ((hqp _).1 hh)).elim ht hs, ?_⟩
    have h3 : algebraMap R S (t * (s * a - i)) ∈ q ^ n := by
      have := Ideal.mem_map_of_mem (algebraMap R S) hta
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ n this
      rw [Ideal.map_le_iff_le_comap, hq]
    rw [RingHom.mem_ker] at hi
    convert h3 using 1
    simp only [map_sub, map_mul, hi]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplSpec
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.exists_prime_over :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      (∀ q : Ideal R, q.IsPrime → q ≤ p → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap (algebraMap R B) = q) ∧
      (∀ a : R, algebraMap R B a = 0 → ∃ s : R, s ∉ p ∧ s * a = 0) := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI := IsCplAt.flat R p B h
  refine ⟨fun q hq hqp => ?_, fun a ha => ?_⟩
  · haveI := hq
    haveI : (maximalIdeal B).LiesOver p := ⟨h.comap_eq.symm⟩
    obtain ⟨P, -, hP, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal B) hqp
    exact ⟨P, hP, hlo.over.symm⟩
  · let Rp := Localization.AtPrime p
    haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
    have hmem : ∀ n : ℕ, algebraMap R Rp a ∈ (maximalIdeal Rp) ^ n := by
      intro n
      obtain ⟨s, hs, hsa⟩ := h.strict n a (by rw [ha]; exact zero_mem _)
      have hu : IsUnit (algebraMap R Rp s) := IsLocalization.map_units Rp (⟨s, hs⟩ : p.primeCompl)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      have := Ideal.mem_map_of_mem (algebraMap R Rp) hsa
      rw [map_mul] at this
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal Rp) (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top
    have h0 : algebraMap R Rp a = 0 := by
      have : algebraMap R Rp a ∈ ⨅ i, (maximalIdeal Rp) ^ i := Ideal.mem_iInf.mpr hmem
      rw [hbot] at this
      exact (Ideal.mem_bot).mp this
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rp a).mp h0
    exact ⟨s, hs, hsa⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerLe
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_le_ker :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (D : Type) [CommRing D] [IsLocalRing D] (φ : P →+* D) [IsLocalHom φ] (l : ι → D),
      l c = 1 → (z.map φ).mulVec l = 0 → (∀ j, φ (m j) = l j * φ (m c)) → genKer z m c ≤ RingHom.ker φ := by
  intro P _ _ ι _ _ z m hcot c D _ _ φ _ l hlc hzl hm
  let ψ : MvPolynomial ι P →+* D := MvPolynomial.eval₂Hom φ l
  have hψC : ∀ a, ψ (MvPolynomial.C a) = φ a := fun a => MvPolynomial.eval₂Hom_C φ l a
  have hlam : ∀ j, ψ (UpperTheory.V.AlgebraTools.lam P c j) = l j := by
    intro j
    unfold UpperTheory.V.AlgebraTools.lam
    split_ifs with h
    · subst h
      simp [hlc]
    · exact MvPolynomial.eval₂Hom_X' φ l j
  let M0 : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P)
  haveI hM0 : M0.IsPrime := UpperTheory.V.AlgebraTools.isPrime_map_C (maximalIdeal P)
  let Q : Ideal (MvPolynomial ι P) := Ideal.comap ψ (maximalIdeal D)
  haveI : Q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal D)
  have hMQ : M0 ≤ Q := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    show ψ (MvPolynomial.C a) ∈ maximalIdeal D
    rw [hψC]
    exact map_nonunit φ a ha
  have hker : chartIdeal z m c ≤ RingHom.ker ψ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ψ (((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i) = 0
      have h := congrFun hzl i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul, hψC, hlam]
      exact h
    · show ψ (MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c)) = 0
      rw [map_sub, map_mul, hψC, hψC, hlam, hm j, sub_self]
  have hchartM : chartIdeal z m c ≤ M0 := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i ∈ M0
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      simpa using hcot.mem (Sum.inl (i, j))
    · show MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c) ∈ M0
      refine Ideal.sub_mem _ (Ideal.mem_map_of_mem _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_))
      · simpa using hcot.mem (Sum.inr j)
      · simpa using hcot.mem (Sum.inr c)
  have hprime := UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime P ι z m hcot c Q hMQ
  have hsat : ∀ x, algebraMap (MvPolynomial ι P) (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) (chartIdeal z m c) →
      ∃ t ∉ Q, t * x ∈ chartIdeal z m c := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl)
      (S := Localization.AtPrime Q) (chartIdeal z m c) x).mp hx
    exact ⟨t, ht, htx⟩
  intro f hf
  obtain ⟨s, hs, hsf⟩ := hf
  have hmem := Ideal.mem_map_of_mem (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) hsf
  rw [map_mul] at hmem
  rcases hprime.mem_or_mem hmem with h | h
  · exfalso
    obtain ⟨t, ht, hts⟩ := hsat s h
    rcases hM0.mem_or_mem (hchartM hts) with h' | h'
    · exact ht (hMQ h')
    · exact hs h'
  · obtain ⟨t, ht, htf⟩ := hsat _ h
    have h0 : ψ (t * MvPolynomial.C f) = 0 := hker htf
    rw [map_mul, hψC] at h0
    have hu : IsUnit (ψ t) := by
      by_contra hn
      exact ht ((IsLocalRing.mem_maximalIdeal _).mpr hn)
    exact (RingHom.mem_ker).mpr ((hu.mul_right_eq_zero).mp h0)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerPrime
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c : ι, (genKer z m c).IsPrime ∧ detIdeal z m ≤ genKer z m c := by
  intro P _ _ ι _ _ z m hind c
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C _
  haveI hJ := chartIdeal_localization_isPrime P ι z m hind c
    (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)) le_rfl
  have key : genKer z m c = Ideal.comap
      ((algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))).comp MvPolynomial.C)
      (Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))) (chartIdeal z m c)) := by
    ext f
    rw [Ideal.mem_comap, RingHom.comp_apply,
      IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).primeCompl]
    exact Iff.rfl
  have sub : ∀ f : P, MvPolynomial.C f ∈ chartIdeal z m c → f ∈ genKer z m c := by
    intro f hf
    rw [key, Ideal.mem_comap, RingHom.comp_apply]
    exact Ideal.mem_map_of_mem _ hf
  have gen : ∀ k, chartGen z m c k ∈ chartIdeal z m c := by
    intro k
    unfold chartIdeal
    exact Ideal.subset_span ⟨k, rfl⟩
  have hinl : ∀ i, ((z.map MvPolynomial.C).mulVec (lam P c)) i ∈ chartIdeal z m c :=
    fun i => gen (Sum.inl i)
  have hinr : ∀ j (h : j ≠ c),
      MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c) ∈ chartIdeal z m c :=
    fun j h => gen (Sum.inr ⟨j, h⟩)
  have hdet : MvPolynomial.C z.det ∈ chartIdeal z m c := by
    have e : ((z.map MvPolynomial.C).adjugate.mulVec
        ((z.map MvPolynomial.C).mulVec (lam P c))) c = MvPolynomial.C z.det := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
        RingHom.map_det]
      simp [lam]
    rw [← e]
    show (∑ i, (z.map MvPolynomial.C).adjugate c i *
      ((z.map MvPolynomial.C).mulVec (lam P c)) i) ∈ _
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hinl i)
  refine ⟨by rw [key]; infer_instance, ?_⟩
  unfold detIdeal relIdeal
  refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (sub _ hdet)))
  rintro _ ⟨i, rfl⟩
  apply sub
  have e : MvPolynomial.C ((z.mulVec m) i) =
      ((z.map MvPolynomial.C).mulVec (lam P c)) i * MvPolynomial.C (m c) +
        ∑ j, MvPolynomial.C (z i j) * (MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul,
      mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  rw [e]
  refine add_mem (Ideal.mul_mem_right _ _ (hinl i)) (Ideal.sum_mem _ fun j _ => ?_)
  by_cases h : j = c
  · simp [h, lam]
  · exact Ideal.mul_mem_left _ _ (hinr j h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaRegPrime
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_localization_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] [IsRegularLocalRing (R ⧸ p)],
      IsRegularLocalRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  intro R _ _ p _ _
  obtain ⟨r, x, hx, hsp⟩ := exists_cotInd_of_regular_quotient R p
  obtain ⟨-, hdim, -⟩ := regular_quotient_cotInd R _ x hx
  obtain ⟨hh, hreg⟩ := regular_localization_cotInd R _ x hx p hsp.symm
  refine ⟨hreg, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hh, add_comm]
  rw [hsp] at hdim
  rw [← hdim]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem finOrb_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K K' L : Subgroup G} (hL : IsCompact (L : Set G)) (hK : K ≤ L) (hK' : IsOpen (K' : Set G)) (x : G) :
    FinOrb K K' x := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : Continuous fun g : G => ((g * x : G) : G ⧸ K') :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hL.image hc).finite_of_discrete).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g, hK g.2, rfl⟩

private theorem iwC_le_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ KO k (Fin n) := by
  refine sup_le (sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right) ?_
  rintro _ ⟨t, ht, rfl⟩
  refine iwahori_le_KO k (Fin n) (diagT_mem_iwahori fun i => ?_)
  obtain ⟨u, -, hu⟩ := ht i trivial
  rw [← hu]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit u)

theorem UpperTheory.V.AlgebraTools.heckePairIwC :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), HeckePair (iwC k n C) ∧ HeckePair (KO k (Fin n)) ∧ ∀ (C' : Subgroup 𝓀[k]ˣ), FinOrb (iwC k n C') (iwC k n C) 1 ∧ FinOrb (KO k (Fin n)) (iwC k n C) 1 := by
  intro k _ _ _ _ n C
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  exact ⟨fun x => finOrb_of_compact hc (iwC_le_KO k n C) ho x,
    fun x => finOrb_of_compact hc le_rfl GlobalTheory.SplitFlip.isOpen_KO x,
    fun C' => ⟨finOrb_of_compact hc (iwC_le_KO k n C') ho 1, finOrb_of_compact hc le_rfl ho 1⟩⟩
end

