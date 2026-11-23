module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultilinearSubMem
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp.DetMod

theorem multilinear_sub_mem {O V W ι : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    [AddCommGroup W] [Module O W] [Fintype ι] [DecidableEq ι]
    (f : (ι → V) →ₘₗ[O] W) (Λ : Submodule O V) (I : Submodule O W)
    (𝔞 : Ideal O) (hI : ∀ z : ι → V, (∀ i, z i ∈ Λ) → f z ∈ I)
    (x y : ι → V) (hx : ∀ i, x i ∈ Λ) (hxy : ∀ i, y i - x i ∈ 𝔞 • Λ) :
    f y - f x ∈ 𝔞 • I := by
  have hy : ∀ i, y i ∈ Λ := fun i => by
    have h1 : y i - x i ∈ Λ := Submodule.smul_le_right (hxy i)
    simpa using Λ.add_mem h1 (hx i)
  have hupd : ∀ (z : ι → V), (∀ i, z i ∈ Λ) → ∀ i, ∀ w ∈ 𝔞 • Λ,
      f (Function.update z i w) ∈ 𝔞 • I := by
    intro z hz i w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro r hr n hn
      rw [f.map_update_smul]
      refine Submodule.smul_mem_smul hr (hI _ fun j => ?_)
      by_cases h : j = i
      · subst h; simpa using hn
      · simpa [Function.update_of_ne h] using hz j
    · intro a b ha hb
      rw [f.map_update_add]
      exact Submodule.add_mem _ ha hb
  have key : ∀ s : Finset ι, f (s.piecewise y x) - f x ∈ 𝔞 • I := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s his ih =>
      have hz : ∀ j, s.piecewise y x j ∈ Λ := fun j => by
        by_cases h : j ∈ s
        · simpa [h] using hy j
        · simpa [h] using hx j
      have h1 := hupd _ hz i _ (hxy i)
      rw [f.map_update_sub] at h1
      have h2 : Function.update (s.piecewise y x) i (x i) = s.piecewise y x := by
        rw [Function.update_eq_self_iff]; simp [his]
      rw [h2] at h1
      rw [Finset.piecewise_insert]
      simpa using Submodule.add_mem _ h1 ih
  simpa using key Finset.univ

theorem mem_of_smul_le {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (I : Submodule O K) (hI : IsFractional (nonZeroDivisors O) I)
    (hI0 : I ≠ ⊥) (𝔞 : Ideal O) (δ : K) (h : ∀ t ∈ I, δ * t ∈ 𝔞 • I) :
    ∃ a ∈ 𝔞, δ = algebraMap O K a := by
  let J : FractionalIdeal (nonZeroDivisors O) K := ⟨I, hI⟩
  have hJ : J ≠ 0 := by
    intro h0
    apply hI0
    have : (J : Submodule O K) = ((0 : FractionalIdeal (nonZeroDivisors O) K) : Submodule O K) := by
      rw [h0]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors O) δ * J
      ≤ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro t ht
    refine Submodule.smul_induction_on (p := fun w => w ∈ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J) (h t ht) ?_ ?_
    · intro r hr n hn
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hn
    · intro a b ha hb
      exact Submodule.add_mem (((𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J : FractionalIdeal _ _) : Submodule O K) ha hb
  have hle2 := mul_le_mul_left hle J⁻¹
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hJ, mul_one, mul_one,
    FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_coeIdeal] at hle2
  obtain ⟨a, ha, rfl⟩ := hle2
  exact ⟨a, ha, rfl⟩

theorem main : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (N : ℕ) (Λ : Submodule O (Fin N → K)) (𝔞 : Ideal O) (γ : Matrix (Fin N) (Fin N) K), Λ.FG → Submodule.span K (Λ : Set (Fin N → K)) = ⊤ → (∀ x ∈ Λ, γ *ᵥ x - x ∈ 𝔞 • Λ) → ∃ a ∈ 𝔞, γ.det = 1 + algebraMap O K a := by
  intro O K _ _ _ _ _ N Λ 𝔞 γ hfg hsp hγ
  let f : (Fin N → Fin N → K) →ₘₗ[O] K :=
    (Matrix.detRowAlternating (n := Fin N) (R := K)).toMultilinearMap.restrictScalars O
  have hf : ∀ z, f z = (Matrix.of z).det := fun z => rfl
  let I : Submodule O K := Submodule.span O {t | ∃ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) ∧ f z = t}
  have hI : ∀ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) → f z ∈ I :=
    fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩

  obtain ⟨d, hd⟩ : ∃ d : nonZeroDivisors O, ∀ x ∈ Λ, ∀ j,
      IsLocalization.IsInteger O ((d : O) • x j) := by
    obtain ⟨S, rfl⟩ := hfg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun p : S × Fin N => (p.1 : Fin N → K) p.2)
    refine ⟨d, fun x hx j => ?_⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact hd (⟨x, hx⟩, j)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x y _ _ hx hy =>
      rw [Pi.add_apply, smul_add]; exact IsLocalization.isInteger_add hx hy
    | smul a x _ hx =>
      rw [Pi.smul_apply, smul_comm]; exact IsLocalization.isInteger_smul hx
  have hfrac : IsFractional (nonZeroDivisors O) I := by
    rw [FractionalIdeal.isFractional_span_iff]
    refine ⟨(d : O) ^ N, pow_mem d.2 N, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    choose m hm using fun i j => hd _ (hz i) j
    refine ⟨(Matrix.of m).det, ?_⟩
    rw [RingHom.map_det, hf, Algebra.smul_def, map_pow]
    have : (algebraMap O K).mapMatrix (Matrix.of m) = algebraMap O K d • Matrix.of z := by
      ext i j
      simp [hm, Algebra.smul_def]
    rw [this, Matrix.det_smul]
    simp
  have hI0 : I ≠ ⊥ := by
    intro h0
    obtain ⟨s, hs, hsp', hli⟩ := exists_linearIndependent K (Λ : Set (Fin N → K))
    rw [hsp] at hsp'
    let b : Module.Basis s K (Fin N → K) := Module.Basis.mk hli (by simp [hsp'])
    let e : s ≃ Fin N := b.indexEquiv (Pi.basisFun K (Fin N))
    let b' := b.reindex e
    have hb' : ∀ i, b' i ∈ Λ := fun i => by
      simp only [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact hs (e.symm i).2
    have h1 := hI b' hb'
    rw [h0, Submodule.mem_bot, hf] at h1
    have h2 : IsUnit (Matrix.of (b' : Fin N → Fin N → K)) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp b'.linearIndependent
    rw [Matrix.isUnit_iff_isUnit_det, h1] at h2
    exact not_isUnit_zero h2
  obtain ⟨a, ha, hδ⟩ := mem_of_smul_le I hfrac hI0 𝔞 (γ.det - 1) (by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h1 := multilinear_sub_mem f Λ I 𝔞 hI z (fun i => γ *ᵥ z i) hz (fun i => hγ _ (hz i))
      have h2 : Matrix.of (fun i => γ *ᵥ z i) = Matrix.of z * γᵀ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      rw [hf, h2, Matrix.det_mul, Matrix.det_transpose, ← hf] at h1
      convert h1 using 1
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx)
  exact ⟨a, ha, by rw [← hδ]; ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.DetMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowEqOneOfIsIntegralOfMulComplexConjEqOne
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : E), IsIntegral ℤ u →
      u * IsCMField.complexConj E u = 1 → ∃ n : ℕ, 0 < n ∧ u ^ n = 1 := by
  intro E _ _ _ u hu h
  have hn : ∀ s : E →+* ℂ, ‖s u‖ = 1 := by
    intro s
    have h1 : s u * (starRingEnd ℂ) (s u) = 1 := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, h, map_one]
    have h2 : ‖s u‖ ^ 2 = 1 := by
      have := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      rw [sq, this]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hu hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowEqOneOfIsIntegralOfMulComplexConjEqOneAlt
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one
    (E : Type) [Field E] [NumberField E] [IsCMField E] (z : E) (hz : IsIntegral ℤ z)
    (h : z * IsCMField.complexConj E z = 1) : ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  have hn : ∀ φ : E →+* ℂ, ‖φ z‖ = 1 := by
    intro φ
    have h1 := congrArg φ h
    rw [map_mul, map_one, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one, RCLike.norm_conj] at h2
    have h0 := norm_nonneg (φ z)
    nlinarith
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hz hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProdNormEmbeddingsEqAbsNorm
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem prod_norm_embeddings_eq_abs_norm (F : Type) [Field F] [NumberField F] (α : F) :
    ∏ σ : F →+* ℂ, ‖σ α‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
  have h2 : ∏ σ : F →+* ℂ, σ α = ∏ σ : F →ₐ[ℚ] ℂ, σ α :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun σ => rfl)
  rw [← norm_prod, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ α, eq_ratCast (algebraMap ℚ ℂ),
    Complex.norm_ratCast, Rat.cast_abs]

theorem norm_finite_embedding_eq_zpow (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (α : F) (k : ℤ)
    (h : v.valuation F α = WithZero.exp (-k)) :
    ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  rw [FinitePlace.norm_embedding', h,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -k)),
    WithZero.log_exp, NNReal.coe_zpow, NNReal.coe_natCast]

theorem sum_log_embeddings_eq (F : Type) [Field F] [NumberField F]
    (n : HeightOneSpectrum (𝓞 F) →₀ ℤ) (α : F) (hα : α ≠ 0)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F α = WithZero.exp (-(n v))) :
    ∑ σ : F →+* ℂ, Real.log ‖σ α‖ =
      n.sum fun v k => (k : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  have hσ : ∀ σ ∈ (Finset.univ : Finset (F →+* ℂ)), ‖σ α‖ ≠ 0 := fun σ _ =>
    norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hα)
  rw [← Real.log_prod hσ, prod_norm_embeddings_eq_abs_norm]
  have hv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) :=
    fun v => norm_finite_embedding_eq_zpow F v α (n v) (hv v)
  have key : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ᶠ w : FinitePlace F, w α := by
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) := by
    simp only [hv2]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hvs
    rw [Function.mem_mulSupport] at hvs
    by_contra hn
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at hn
    apply hvs
    simp [hn]
  have E0 := FinitePlace.prod_eq_inv_abs_norm hα
  rw [← key, hprod] at E0
  have hfac : ∀ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) ≠ 0 := by
    intro v _
    apply zpow_ne_zero
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have L := congrArg Real.log E0
  push_cast at L ⊢
  rw [Real.log_prod hfac, Real.log_inv] at L
  simp only [Real.log_zpow] at L
  rw [Finsupp.sum]
  have hneg : ∑ v ∈ n.support, ((-(n v) : ℤ) : ℝ) * Real.log (Ideal.absNorm v.asIdeal)
      = -∑ v ∈ n.support, (n v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    push_cast
    ring
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RealOfFixedByConjugations
section
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.UnimodularBaseChange

theorem bijective_baseChange :
    ∀ (Z : Type) [CommRing Z] (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
      (B : LinearMap.BilinForm ℤ L), Function.Bijective B →
      Function.Bijective (B.baseChange Z) := by
  intro Z _ L _ _ _ B hB
  classical
  let b := Module.Free.chooseBasis ℤ L
  let c := b.baseChange Z
  have h1 : IsUnit (LinearMap.toMatrix b b.dualBasis B).det :=
    LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have h2 : LinearMap.toMatrix c c.dualBasis (B.baseChange Z) =
      (algebraMap ℤ Z).mapMatrix (LinearMap.toMatrix b b.dualBasis B) := by
    ext i j
    simp [c, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  have h3 : IsUnit (LinearMap.toMatrix c c.dualBasis (B.baseChange Z)).det := by
    rw [h2, ← RingHom.map_det]
    exact h1.map _
  exact (LinearEquiv.ofIsUnitDet h3).bijective

end GlobalTheory.CompanionTheory.UnimodularBaseChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootOfUnityEqOneOfSubOneMemSpan
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem rootOfUnity_eq_one_of_sub_one_mem_span : ∀ (E : Type) [Field E] [NumberField E] (z : 𝓞 E) (n M : ℕ), 0 < n → 3 ≤ M → z ^ n = 1 → z - 1 ∈ Ideal.span {(M : 𝓞 E)} → z = 1 := by
  intro E _ _ z n M hn hM hz hmem
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  suffices hw0 : w = 0 by
    rw [hw0, zero_mul] at hw
    exact sub_eq_zero.mp hw.symm
  have hMpos : (0 : ℝ) < M := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hzE : (z : E) ^ n = 1 := by
    have h := congrArg (algebraMap (𝓞 E) E) hz
    rw [map_pow, map_one] at h
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact h
  have hwE : (w : E) * (M : E) = (z : E) - 1 := by
    have h := congrArg (algebraMap (𝓞 E) E) hw
    rw [map_mul, RingHom.map_sub, map_natCast, map_one] at h
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap w, NumberField.RingOfIntegers.coe_eq_algebraMap z]
    exact h
  have hbound : ∀ σ : E →ₐ[ℚ] ℂ, ‖σ (w : E)‖ ≤ 2 / M := by
    intro σ
    have hz1 : ‖σ (z : E)‖ = 1 := by
      have h1 : ‖σ (z : E)‖ ^ n = 1 := by
        rw [← norm_pow, ← map_pow, hzE, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1
    have h2 : σ (w : E) * (M : ℂ) = σ (z : E) - 1 := by
      have h := congrArg σ hwE
      rw [map_mul, map_sub, map_natCast, map_one] at h
      exact h
    have h3 : ‖σ (w : E)‖ * (M : ℝ) ≤ 2 := by
      have h4 : ‖σ (w : E) * (M : ℂ)‖ = ‖σ (w : E)‖ * (M : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
      rw [← h4, h2]
      calc ‖σ (z : E) - 1‖ ≤ ‖σ (z : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hz1, norm_one]; norm_num
    exact (le_div_iff₀ hMpos).mpr h3
  have hcard : Fintype.card (E →ₐ[ℚ] ℂ) ≠ 0 := by
    rw [AlgHom.card ℚ E ℂ]
    exact (Module.finrank_pos).ne'
  have hprod : ‖((Algebra.norm ℤ w : ℤ) : ℂ)‖ < 1 := by
    have h1 : ((Algebra.norm ℤ w : ℤ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (w : E)) := by
      rw [← Algebra.coe_norm_int, map_intCast]
    rw [h1, Algebra.norm_eq_prod_embeddings ℚ ℂ (w : E), norm_prod]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (w : E)‖ ≤ ∏ _σ : E →ₐ[ℚ] ℂ, (2 / M : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun σ _ => hbound σ)
      _ = (2 / M : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) := by rw [Finset.prod_const, Finset.card_univ]
      _ < 1 := pow_lt_one₀ (by positivity) ((div_lt_one hMpos).mpr (by linarith)) hcard
  have hN : Algebra.norm ℤ w = 0 := by
    rw [Complex.norm_intCast] at hprod
    have habs : ((|Algebra.norm ℤ w| : ℤ) : ℝ) < 1 := by
      push_cast
      exact hprod
    have habs' : |Algebra.norm ℤ w| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp habs'
  exact Algebra.norm_eq_zero_iff.mp hN

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotient
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.QuotientSide

theorem isSeparated_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S)
    (r : X ⟶ Y) (w : r ≫ g = f) [IsSeparated f] [IsFinite r] [Surjective r] : IsSeparated g := by
  subst w
  let m : pullback (r ≫ g) (r ≫ g) ⟶ pullback g g :=
    pullback.map _ _ _ _ r r (𝟙 S) (by simp) (by simp)
  have hm : IsFinite m :=
    MorphismProperty.pullbackMap (P := @IsFinite) (i₁ := r) (i₂ := r) inferInstance inferInstance
      rfl rfl
  have comm : pullback.diagonal (r ≫ g) ≫ m = r ≫ pullback.diagonal g := by
    have h₁ : m ≫ pullback.fst g g = pullback.fst (r ≫ g) (r ≫ g) ≫ r := pullback.lift_fst _ _ _
    have h₂ : m ≫ pullback.snd g g = pullback.snd (r ≫ g) (r ≫ g) ≫ r := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, pullback.diagonal_fst,
        pullback.diagonal_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, pullback.diagonal_snd,
        pullback.diagonal_snd, Category.id_comp, Category.comp_id]
  have hrange : Set.range (pullback.diagonal g) =
      m '' Set.range (pullback.diagonal (r ≫ g)) := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, comm,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr r.surjective, Set.image_univ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact m.isClosedMap _ (pullback.diagonal (r ≫ g)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

theorem isSeparated_target_of_finite_surjective :
    ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q →
      IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left →
      IsSeparated Y.hom := by
  intro S X Y K q p₁ p₂ _ _ hX hq hs
  exact isSeparated_of_finite_surjective X.hom Y.hom q.left (Over.w q)

end GlobalTheory.CompanionTheory.QuotientSide
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticUnipotentShape
section
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem symplectic_unipotent_shape : ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ), (∀ x, B x x = 0) → (∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 ∧ B (bas (.inr i)) (bas (.inr j)) = 0 ∧ B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0) → ∀ T : Λ →ₗ[ℤ] Λ, (∀ x y, B (T x) (T y) = B x y) → (∀ i, T (bas (.inl i)) = bas (.inl i)) → ∃ N : Matrix (Fin g) (Fin g) ℤ, Nᵀ = N ∧ ∀ j, T (bas (.inr j)) = bas (.inr j) + ∑ k, N j k • bas (.inl k) := by
  intro g Λ _ B bas halt hB T hT hTa
  have hB1 : ∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 := fun i j => (hB i j).1
  have hB2 : ∀ i j, B (bas (.inr i)) (bas (.inr j)) = 0 := fun i j => (hB i j).2.1
  have hB3 : ∀ i j, B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0 :=
    fun i j => (hB i j).2.2
  have skew : ∀ x y, B x y = -B y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
    linarith
  have hexp : ∀ v : Λ, v = ∑ k, bas.repr v (.inl k) • bas (.inl k) +
      ∑ k, bas.repr v (.inr k) • bas (.inr k) := by
    intro v
    conv_lhs => rw [← bas.sum_repr v]
    rw [Fintype.sum_sum_type]
  have pa : ∀ i v, B (bas (.inl i)) v = bas.repr v (.inr i) := by
    intro i v
    conv_lhs => rw [hexp v]
    simp [hB1, hB3]
  have pb : ∀ i v, B (bas (.inr i)) v = -bas.repr v (.inl i) := by
    intro i v
    have hba : ∀ k, B (bas (.inr i)) (bas (.inl k)) = -(if k = i then 1 else 0) :=
      fun k => by rw [skew, hB3]
    conv_lhs => rw [hexp v]
    simp [hba, hB2]
  have hd : ∀ i j, bas.repr (T (bas (.inr j))) (.inr i) = if i = j then 1 else 0 := by
    intro i j
    rw [← pa, ← hTa i, hT, hB3]
  have hTb : ∀ j, T (bas (.inr j)) =
      bas (.inr j) + ∑ k, bas.repr (T (bas (.inr j))) (.inl k) • bas (.inl k) := by
    intro j
    conv_lhs => rw [hexp (T (bas (.inr j)))]
    rw [add_comm]
    congr 1
    simp [hd, ite_smul]
  refine ⟨fun j k => bas.repr (T (bas (.inr j))) (.inl k), ?_, hTb⟩
  ext i j
  show bas.repr (T (bas (.inr j))) (.inl i) = bas.repr (T (bas (.inr i))) (.inl j)
  have h0 : B (T (bas (.inr j))) (T (bas (.inr i))) = 0 := by rw [hT, hB2]
  rw [hTb j, map_add (f := _), LinearMap.add_apply, pb j] at h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, pa, hd] at h0
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TelescopingCoordinateDifference
section
namespace GlobalTheory.CompanionTheory.Telescope

theorem telescope_fin_positions (α : Type) (n : ℕ) (F : (Fin n → α) → ℝ) (a b : Fin n → α) :
    F a - F b = ∑ i : Fin n, (F (fun j => if j < i then b j else a j) - F (fun j => if j ≤ i then b j else a j)) := by
  classical
  set G : ℕ → ℝ := fun m => F (fun j => if (j : ℕ) < m then b j else a j) with hG
  have h0 : G 0 = F a := by simp [hG]
  have hn : G n = F b := by simp [hG]
  rw [← h0, ← hn, ← Finset.sum_range_sub' G n, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hG, Nat.lt_succ_iff, Fin.lt_def, Fin.le_def]

end GlobalTheory.CompanionTheory.Telescope
end

