module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt
section
noncomputable section

namespace Formalism.L2.LamCM

open Polynomial IsLocalRing

theorem exists_monic_irreducible_card_gt (k : Type) [Field k] [Finite k] (N : ℕ) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ N < Nat.card (AdjoinRoot f) := by
  classical

  have hcard : ∀ f : k[X], f.Monic → Nat.card (AdjoinRoot f) = Nat.card k ^ f.natDegree := by
    intro f hf
    rw [Nat.card_congr (AdjoinRoot.powerBasis hf.ne_zero).basis.equivFun.toEquiv, Nat.card_fun]
    simp [AdjoinRoot.powerBasis_dim]
  by_contra hcon
  push_neg at hcon
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card

  have hdeg : ∀ α : AlgebraicClosure k, (minpoly k α).natDegree ≤ N := by
    intro α
    have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    have h1 := hcon _ (minpoly.monic hint) (minpoly.irreducible hint)
    rw [hcard _ (minpoly.monic hint)] at h1
    have h2 : (minpoly k α).natDegree < 2 ^ (minpoly k α).natDegree := Nat.lt_two_pow_self
    have h3 : 2 ^ (minpoly k α).natDegree ≤ Nat.card k ^ (minpoly k α).natDegree := Nat.pow_le_pow_left hq _
    omega
  have hsub : (Set.univ : Set (AlgebraicClosure k)) ⊆ ⋃ c : Fin (N + 1) → k,
      (∑ i : Fin (N + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).rootSet (AlgebraicClosure k) := by
    intro α _
    have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    refine Set.mem_iUnion.2 ⟨fun i => (minpoly k α).coeff i, ?_⟩
    have hp : (∑ i : Fin (N + 1), Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ (i : ℕ)) = minpoly k α := by
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C ((minpoly k α).coeff i) * Polynomial.X ^ i)]
      conv_rhs => rw [Polynomial.as_sum_range' (minpoly k α) (N + 1) (by have := hdeg α; omega)]
      simp only [Polynomial.C_mul_X_pow_eq_monomial]
    rw [hp, Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval k α⟩
  have hfin : (Set.univ : Set (AlgebraicClosure k)).Finite :=
    Set.Finite.subset (Set.finite_iUnion fun c => Polynomial.rootSet_finite _ _) hsub
  have : Finite (AlgebraicClosure k) := Set.finite_univ_iff.1 hfin
  exact not_finite (AlgebraicClosure k)

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ J • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun x => b.repr x i ∈ J) hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · simp only [map_add (f := _), Finsupp.add_apply]
      exact J.add_mem hx hy
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem mem_smul_top_self_iff {R : Type} [CommRing R] (J : Ideal R) (y : R) :
    y ∈ J • (⊤ : Submodule R R) ↔ y ∈ J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem isAdicComplete_of_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (I : Ideal R) (b : Module.Basis ι R M) (h : IsAdicComplete I R) : IsAdicComplete I M := by

  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    simp only [map_sub, Finsupp.sub_apply, SModEq.sub_mem, mem_smul_top_self_iff]
  haveI := h
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    have h0 : ∀ i, b.repr x i = 0 := fun i =>
      IsHausdorff.haus' (I := I) (b.repr x i) fun n => by simpa using (key n x 0).1 (hx n) i
    exact b.repr.injective (Finsupp.ext fun i => by simpa using h0 i)
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
      IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have hr : b.repr (b.equivFun.symm L) i = L i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hr]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

def quotResidueEquiv {V : Type} [CommRing V] [IsLocalRing V] (g : V[X]) :
    AdjoinRoot g ⧸ Ideal.map (algebraMap V (AdjoinRoot g)) (maximalIdeal V) ≃+*
      AdjoinRoot (g.map (residue V)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal V) g

theorem largeResidueExtension : BigResExt := by
  intro V _ _ _ hV _ N
  obtain ⟨gb, hgbm, hgbi, hN⟩ := exists_monic_irreducible_card_gt (ResidueField V) N
  obtain ⟨g, hgmap, hgdeg, hg⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).2 (map_surjective (residue V) residue_surjective gb)) hgbm
  subst hgmap
  set W := AdjoinRoot g
  have hirr : Irreducible g := Monic.irreducible_of_irreducible_map (residue V) g hg hgbi
  have hdom : IsDomain W := AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hirr)
  let pb := AdjoinRoot.powerBasis' hg
  have : Module.Finite V W := pb.finite
  have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  set M0 : Ideal W := Ideal.map (algebraMap V W) (maximalIdeal V) with hM0def
  have : Fact (Irreducible (g.map (residue V))) := ⟨hgbi⟩
  have hM0 : M0.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).2
    (MulEquiv.isField (Field.toIsField (AdjoinRoot (g.map (residue V)))) (quotResidueEquiv g).toMulEquiv)
  have hloc : IsLocalRing W := IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM => by
    letI := hM
    have hc : (M.comap (algebraMap V W)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap V W)
        (fun x => Algebra.IsIntegral.isIntegral x) M
    have h1 := eq_maximalIdeal hc
    have hle : M0 ≤ M := by
      rw [hM0def, ← h1]
      exact Ideal.map_comap_le
    exact (hM0.eq_of_le hM.ne_top hle).symm⟩
  have hmax : maximalIdeal W = M0 := (eq_maximalIdeal hM0).symm
  have hdeg : g.degree ≠ 0 := by
    intro h
    have h0 : g.natDegree = 0 := by rw [natDegree_eq_zero_iff_degree_le_zero, h]
    have := hgbi.natDegree_pos
    omega
  have hinj : Function.Injective (algebraMap V W) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  obtain ⟨⟨ϖ, hϖ⟩⟩ := IsPrincipalIdealRing.principal (maximalIdeal V)
  have hprin : (maximalIdeal W).IsPrincipal := by
    refine ⟨⟨algebraMap V W ϖ, ?_⟩⟩
    rw [hmax, hM0def, hϖ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField W := by
    intro hf
    have h1 : maximalIdeal W = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hf
    rw [hmax, hM0def, Ideal.map_eq_bot_iff_of_injective hinj] at h1
    exact IsDiscreteValuationRing.not_a_field V h1
  have hdvr : IsDiscreteValuationRing W := ((IsDiscreteValuationRing.TFAE W hnf).out 1 5).2 hprin
  have ecard : Nat.card (ResidueField W) = Nat.card (AdjoinRoot (g.map (residue V))) :=
    Nat.card_congr ((Ideal.quotEquivOfEq hmax).trans (quotResidueEquiv g)).toEquiv
  refine ⟨W, inferInstance, hdom, hdvr, inferInstance, ?_, ?_, ?_, hinj, ?_⟩
  · rw [hmax, hM0def, IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_basis _ pb.basis hV
  · exact Nat.finite_of_card_ne_zero (by omega)
  · omega
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal V := (mem_maximalIdeal a).2 hna
    have h2 : algebraMap V W a ∈ maximalIdeal W := by
      rw [hmax]; exact Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 ha

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

section general

variable {K : Type} [Field K] [NumberField K]

lemma absNorm_pos' {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (0 : ℝ) < ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have h1 := FractionalIdeal.absNorm_nonneg I
  have h2 : (FractionalIdeal.absNorm I : ℚ) ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)

lemma log_absNorm_mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Real.log ((FractionalIdeal.absNorm (I * J) : ℚ) : ℝ) =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) + Real.log ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
  rw [map_mul, Rat.cast_mul, Real.log_mul (absNorm_pos' hI).ne' (absNorm_pos' hJ).ne']

lemma mul_le_mul_r {A B : FractionalIdeal (𝓞 K)⁰ K} (h : A ≤ B) (C : FractionalIdeal (𝓞 K)⁰ K) :
    A * C ≤ B * C :=
  mul_le_mul' h le_rfl

lemma spanSingleton_ne_zero' {x : K} (hx : x ≠ 0) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
  rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

lemma le_one_mul {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≤ 1) (hB : B ≤ 1) : A * B ≤ 1 := by
  obtain ⟨A0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hA
  obtain ⟨B0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hB
  rw [← FractionalIdeal.coeIdeal_mul]
  exact FractionalIdeal.coeIdeal_le_one

lemma valuation_algebraMap_eq (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (algebraMap (𝓞 K) K r) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg hr,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v (by simpa using hr)]

lemma valuation_eq_exp_count (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (𝓞 K)⁰ x
  simp only at hrs
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hr : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hrs
    exact mul_ne_zero hx hs0 hrs
  have hv : v.valuation K x * v.valuation K (algebraMap (𝓞 K) K s) = v.valuation K (algebraMap (𝓞 K) K r) := by
    rw [← map_mul, hrs]
  have hc : FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) +
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K s)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) := by
    rw [← FractionalIdeal.count_mul K v (spanSingleton_ne_zero' hx) (spanSingleton_ne_zero' hs0),
      FractionalIdeal.spanSingleton_mul_spanSingleton, hrs]
  rw [valuation_algebraMap_eq v hs, valuation_algebraMap_eq v hr, ← hc, neg_add, WithZero.exp_add] at hv
  exact mul_right_cancel₀ WithZero.exp_ne_zero hv

lemma le_one_of_count_nonneg {J : FractionalIdeal (𝓞 K)⁰ K} (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb => le_one_mul ha hb) (fun v => ?_)
  show (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v J ≤ 1
  rw [← Int.toNat_of_nonneg (h v), zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

end general

theorem degree_algebraic : DegAlg := by
  intro K _ _ L M hL hM
  obtain ⟨hLI, hLn⟩ := hL
  obtain ⟨hMI, hMn⟩ := hM
  refine ⟨⟨mul_ne_zero hLI hMI, fun σ => mul_pos (hLn σ) (hMn σ)⟩, ?_,
    ⟨inv_ne_zero hLI, fun σ => inv_pos.mpr (hLn σ)⟩, ?_,
    fun k => ⟨⟨pow_ne_zero _ hLI, fun σ => pow_pos (hLn σ) k⟩, ?_⟩⟩
  · simp only [MLine.deg, MLine.tensor]
    rw [log_absNorm_mul hLI hMI,
      Finset.sum_congr rfl (fun σ _ => Real.log_mul (hLn σ).ne' (hMn σ).ne'), Finset.sum_add_distrib]
    ring
  · simp only [MLine.deg, MLine.dual]
    rw [map_inv₀, Rat.cast_inv, Real.log_inv,
      Finset.sum_congr rfl (fun σ _ => Real.log_inv (L.n σ)), Finset.sum_neg_distrib]
    ring
  · simp only [MLine.deg, MLine.pow]
    rw [map_pow, Rat.cast_pow, Real.log_pow,
      Finset.sum_congr rfl (fun σ _ => Real.log_pow (L.n σ) k), ← Finset.mul_sum]
    ring

theorem mem_of_loc' : MemOfLoc := by
  intro K _ _ I x hI hloc
  by_cases hx : x = 0
  · rw [hx]; exact FractionalIdeal.zero_mem I
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hge : ∀ p : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K p I ≤ FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
    intro p
    obtain ⟨c, ⟨hc0, hcount⟩, hle⟩ := hloc p
    rw [valuation_eq_exp_count p hx, valuation_eq_exp_count p hc0, WithZero.exp_le_exp, hcount] at hle
    linarith
  set J := FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I⁻¹ with hJdef
  have hJ0 : J ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
  have hJ : J ≤ 1 := by
    refine le_one_of_count_nonneg hJ0 fun p => ?_
    rw [hJdef, FractionalIdeal.count_mul K p hs (inv_ne_zero hI), FractionalIdeal.count_inv]
    linarith [hge p]
  have hJI : J * I = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    rw [hJdef, mul_assoc, inv_mul_cancel₀ hI, mul_one]
  rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hJI]
  calc J * I ≤ 1 * I := mul_le_mul_r hJ I
    _ = I := one_mul I

end Formalism.L2.LamCM
end
end

