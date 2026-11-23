module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdele
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdIdem

theorem local_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (s : K) :
    ∃ e : K, (e = 0 ∨ e = 1) ∧ w (1 + 1) ≤ w (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : (1 + 1 : K) = (1 + s) + (1 - s) := by ring
  have h := w.map_add (1 + s) (1 - s)
  rw [← h2] at h
  rcases le_total (w (1 - s)) (w (1 + s)) with hle | hle
  · refine ⟨1, Or.inr rfl, ?_⟩
    rw [max_eq_left hle] at h
    simpa using h
  · refine ⟨0, Or.inl rfl, ?_⟩
    rw [max_eq_right hle] at h
    simpa using h

theorem local_field {K : Type*} [Field K] (h2 : (1 + 1 : K) ≠ 0) (s : K) :
    ∃ e : K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  by_cases h : 1 + s = 0
  · refine ⟨0, by simp, ?_⟩
    rw [isUnit_iff_ne_zero]
    intro h'
    apply h2
    linear_combination h + h'
  · exact ⟨1, by simp, by simpa [isUnit_iff_ne_zero] using h⟩

theorem finite_part (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (s : FiniteAdeleRing R K) :
    ∃ e : FiniteAdeleRing R K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have hu : IsUnit (1 + 1 : FiniteAdeleRing R K) := by
    have : IsUnit (1 + 1 : K) := by
      rw [isUnit_iff_ne_zero]; norm_num
    simpa using this.map (algebraMap K (FiniteAdeleRing R K))
  rw [FiniteAdeleRing.isUnit_iff] at hu
  choose e he hv using fun v : HeightOneSpectrum R =>
    local_val (Valued.v : Valuation (v.adicCompletion K) _) (s v)
  have hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K := by
    intro v
    rcases he v with h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
  let E : FiniteAdeleRing R K := ⟨e, Filter.Eventually.of_forall hint⟩
  refine ⟨E, ?_, ?_⟩
  · refine FiniteAdeleRing.ext K fun v => ?_
    change e v * e v = e v
    rcases he v with h | h <;> simp [h]
  · have hval : ∀ v : HeightOneSpectrum R, Valued.v ((1 + 1 : FiniteAdeleRing R K) v) ≤
        Valued.v ((E * (1 + s) + (1 - E) * (1 - s)) v) := fun v => hv v
    rw [FiniteAdeleRing.isUnit_iff]
    refine ⟨fun v h0 => ?_, ?_⟩
    · have := hval v
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
      exact hu.1 v this
    · filter_upwards [hu.2, (E * (1 + s) + (1 - E) * (1 - s)).2] with v h1 h2
      exact le_antisymm h2 (h1 ▸ hval v)

theorem infinite_part (K : Type*) [Field K] [CharZero K] (s : InfiniteAdeleRing K) :
    ∃ e : InfiniteAdeleRing K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : ∀ v : InfinitePlace K, (1 + 1 : v.Completion) ≠ 0 := by
    intro v h
    have : algebraMap K v.Completion (1 + 1) = 0 := by rw [map_add (f := _), map_one]; exact h
    rw [map_eq_zero] at this
    norm_num at this
  choose e he hu using fun v : InfinitePlace K => local_field (h2 v) (s v)
  exact ⟨e, funext he, Pi.isUnit_iff.2 hu⟩

theorem exists_idem_isUnit (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F) :
    ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  obtain ⟨e₁, h₁, u₁⟩ := infinite_part F s.1
  obtain ⟨e₂, h₂, u₂⟩ := finite_part (𝓞 F) F s.2
  exact ⟨(e₁, e₂), Prod.ext h₁ h₂, Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩

end GlobalTheory.AdIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ImportsTer
section
open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LocalNormBound

theorem local_bound (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (W : Set (v.adicCompletion F)) (hW : W ∈ 𝓝 (0 : v.adicCompletion F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ v.adicCompletionIntegers F, N • x ∈ W := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hW
  have hp : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  set p := Ideal.absNorm v.asIdeal with hpdef
  have hlt : Valued.v ((p : ℕ) : v.adicCompletion F) < 1 := by
    have h1 : ((p : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by
      simp
    rw [h1]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (p : 𝓞 F))
    have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 (Ideal.absNorm_mem _)
    exact h2 ▸ h3
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hlt
  have hS := Valued.mem_nhds_zero.2 ⟨γ, subset_rfl (a := _)⟩
  obtain ⟨n, hn⟩ := (ht.eventually hS).exists
  refine ⟨p ^ n, pow_pos hp n, fun x hx => hγ ?_⟩
  refine lt_of_le_of_lt ?_ hn
  rw [Valuation.restrict_le_iff, nsmul_eq_mul, map_mul, Nat.cast_pow]
  exact mul_le_of_le_one_right' hx

theorem main : ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F], ∀ U ∈ nhds (0 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), ∃ (N : ℕ), (0 : ℕ) < N ∧ ∀ (a : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (a : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion F a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) → N • a ∈ U := by
  intro F _ _ U hU
  classical
  let φ : (Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
      FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hφ : Continuous φ := RestrictedProduct.isEmbedding_structureMap.continuous
  let z : Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨0, zero_mem _⟩
  have hz : φ z = 0 := FiniteAdeleRing.ext F fun v => rfl
  have h1 : φ ⁻¹' U ∈ 𝓝 z := hφ.continuousAt.preimage_mem_nhds (hz ▸ hU)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  have h2 : ∀ v : HeightOneSpectrum (𝓞 F), ∃ N : ℕ, 0 < N ∧
      ∀ x (hx : x ∈ v.adicCompletionIntegers F), ⟨N • x, nsmul_mem hx N⟩ ∈ t v := by
    intro v
    obtain ⟨W, hW, hWt⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨N, hN, h⟩ := local_bound F v W hW
    exact ⟨N, hN, fun x hx => hWt (h x hx)⟩
  choose n hn hnt using h2
  refine ⟨∏ v ∈ hI.toFinset, n v, Finset.prod_pos fun v _ => hn v, fun a ha => ?_⟩
  set N := ∏ v ∈ hI.toFinset, n v with hN
  have h3 : φ (fun v => ⟨N • a v, nsmul_mem (ha v) N⟩) = N • a :=
    FiniteAdeleRing.ext F fun v => rfl
  rw [← h3]
  refine hsub fun v hv => ?_
  obtain ⟨k, hk⟩ : n v ∣ N := Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv)
  have h4 := hnt v (k • a v) (nsmul_mem (ha v) k)
  convert h4 using 2
  rw [hk, mul_smul]

end GlobalTheory.LocalNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.InfAdeleCM

variable {F : Type} [Field F] [NumberField F]

def ext (σ : F →+* ℂ) : InfiniteAdeleRing F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) (InfinitePlace.mk σ))

theorem ext_apply (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ) (a (InfinitePlace.mk σ)) := rfl

theorem continuous_ext (σ : F →+* ℂ) : Continuous (ext σ) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk σ)).continuous.comp
    (continuous_apply (InfinitePlace.mk σ))

theorem ext_algebraMap [IsTotallyReal F] (σ : F →+* ℂ) (x : F) :
    ext σ (algebraMap F (InfiniteAdeleRing F) x) = σ x := by
  have h : (InfinitePlace.mk σ).embedding = σ :=
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ)
  rw [ext_apply, InfiniteAdeleRing.algebraMap_apply]
  simp [h]

theorem ext_eq_ofReal [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal (InfinitePlace.mk σ)) (a (InfinitePlace.mk σ)) : ℝ) := by
  rw [ext_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

theorem conj_ext [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    starRingEnd ℂ (ext σ a) = ext σ a := by
  rw [ext_eq_ofReal, Complex.conj_ofReal]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem exists_hom [IsTotallyReal F] (τ : E →+* ℂ) :
    ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧
      Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)) := by
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : InfiniteAdeleRing F →ₐ[F] ℂ :=
    { ext (τ.comp (algebraMap F E)) with commutes' := fun x => ext_algebraMap _ x }
  let g : E →ₐ[F] ℂ := { τ with commutes' := fun x => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, ?_, ?_⟩
  · intro x
    simp [g]
  · have : (fun a : InfiniteAdeleRing F =>
        (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom (a ⊗ₜ (1 : E))) =
        ext (τ.comp (algebraMap F E)) := by
      funext a
      simp [f]
    rw [this]
    exact continuous_ext _

theorem hom_tmul [IsTotallyReal F] (τ : E →+* ℂ) (θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ)
    (h1 : ∀ x, θ (1 ⊗ₜ x) = τ x) (h2 : Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)))
    (a : InfiniteAdeleRing F) (x : E) :
    θ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x := by
  have : (fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) = ext (τ.comp (algebraMap F E)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h2 (continuous_ext _) ?_
    funext y
    simp only [Function.comp_apply, ext_algebraMap, RingHom.comp_apply]
    rw [← h1, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [← this, ← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem exists_delta (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) :
    ∃ δ : E, δ ≠ 0 ∧ c δ = -δ ∧ ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push_neg at h
    exact hc (AlgEquiv.ext h)
  have hcc : c (c y) = y := τ.injective (by rw [hτ, hτ, Complex.conj_conj])
  have hδ : y - c y ≠ 0 := sub_ne_zero.2 hy.symm
  have hcδ : c (y - c y) = -(y - c y) := by rw [map_sub, hcc]; ring
  refine ⟨y - c y, hδ, hcδ, ?_⟩
  generalize y - c y = δ at hδ hcδ
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg c hst
    have hsm : ∀ (p : F) (x : E), c (p • x) = p • c x := fun p x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, c.commutes]
    rw [map_add (f := _), hsm, hsm, map_one, hcδ, map_zero, smul_neg] at h'
    have ht : t • δ = 0 := by
      have : (2 : E) * (t • δ) = 0 := by linear_combination hst - h'
      simpa using this
    have ht' : t = 0 := by simpa [hδ] using ht
    refine ⟨?_, ht'⟩
    simpa [ht'] using hst
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  intro x
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hx
  obtain ⟨p, q, rfl⟩ := hx
  exact ⟨p, q, by simp [Algebra.smul_def]⟩

theorem eq_or_conj (c : E ≃ₐ[F] E) (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    {δ : E} (h0 : δ ≠ 0) (hc : c δ = -δ)
    (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ) (τ τ' : E →+* ℂ)
    (h : τ.comp (algebraMap F E) = τ'.comp (algebraMap F E)) :
    τ = τ' ∨ τ = ComplexEmbedding.conjugate τ' := by
  have hp : ∀ p, τ (algebraMap F E p) = τ' (algebraMap F E p) := fun p => RingHom.congr_fun h p
  obtain ⟨p, q, hpq⟩ := hs (δ * δ)
  have h' := congrArg c hpq
  rw [map_mul, map_add (f := _), map_mul, hc, c.commutes, c.commutes] at h'
  have hsq : δ * δ = algebraMap F E p := by linear_combination (hpq + h') / 2
  have : τ δ * τ δ = τ' δ * τ' δ := by rw [← map_mul, ← map_mul, hsq, hp]
  rcases mul_self_eq_mul_self_iff.1 this with e | e
  · left
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    simp [hp, e]
  · right
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hτ]
    simp [hp, e, hc]

theorem exists_decomp {δ : E} (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ)
    (z : InfiniteAdeleRing F ⊗[F] E) : ∃ a b : InfiniteAdeleRing F, z = a ⊗ₜ 1 + b ⊗ₜ δ := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨p, q, rfl⟩ := hs x
    refine ⟨p • a, q • a, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

theorem mk_eq_iff [IsTotallyReal F] {σ σ' : F →+* ℂ} (h : InfinitePlace.mk σ = InfinitePlace.mk σ') : σ = σ' := by
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ')]

theorem exists_over [IsTotallyReal F] (Ψ : Set (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : InfinitePlace F) :
    ∃ τ ∈ Ψ, InfinitePlace.mk (τ.comp (algebraMap F E)) = w := by
  have h : InfinitePlace.mk ((ComplexEmbedding.lift E w.embedding).comp (algebraMap F E)) = w := by
    rw [ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding]
  by_cases hm : ComplexEmbedding.lift E w.embedding ∈ Ψ
  · exact ⟨_, hm, h⟩
  · refine ⟨ComplexEmbedding.conjugate (ComplexEmbedding.lift E w.embedding), ?_, ?_⟩
    · by_contra hn
      exact hm ((hΨ _).2 hn)
    · rw [← h, ← InfinitePlace.mk_conjugate_eq]
      congr 1
      ext x
      simp

theorem bijective [IsTotallyReal F] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    (θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (hθ : ∀ τ a x, θ τ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  obtain ⟨δ, h0, hcδ, hs⟩ := exists_delta c h2 hc hτ
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hτ τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact h0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ w : InfinitePlace F, w.Completion →+* ℝ := fun w =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
  have hr : ∀ w, Function.Bijective (r w) := fun w =>
    InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal _
  have hval : ∀ (τ : E →+* ℂ) (a b : InfiniteAdeleRing F), θ τ (a ⊗ₜ 1 + b ⊗ₜ δ) =
      ⟨r _ (a (InfinitePlace.mk (τ.comp (algebraMap F E)))),
        r _ (b (InfinitePlace.mk (τ.comp (algebraMap F E)))) * (τ δ).im⟩ := by
    intro τ a b
    rw [map_add (f := _), hθ, hθ, ext_eq_ofReal, ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, r]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, r]
  choose t ht htw using exists_over (F := F) Ψ hΨ
  constructor
  · intro z z' hz
    obtain ⟨a, b, rfl⟩ := exists_decomp hs z
    obtain ⟨a', b', rfl⟩ := exists_decomp hs z'
    have key : ∀ w, a w = a' w ∧ b w = b' w := by
      intro w
      have := congrFun hz ⟨t w, ht w⟩
      simp only [hval, Complex.mk.injEq] at this
      rw [htw w] at this
      exact ⟨(hr w).1 this.1, (hr w).1 (mul_right_cancel₀ (him _) this.2)⟩
    have ha : a = a' := funext fun w => (key w).1
    have hb : b = b' := funext fun w => (key w).2
    rw [ha, hb]
  · intro y
    choose a ha using fun w => (hr w).2 (y ⟨t w, ht w⟩).re
    choose b hb using fun w => (hr w).2 ((y ⟨t w, ht w⟩).im / (t w δ).im)
    refine ⟨(show InfiniteAdeleRing F from a) ⊗ₜ[F] (1 : E) + (show InfiniteAdeleRing F from b) ⊗ₜ[F] δ, ?_⟩
    funext τ
    obtain ⟨τ, hτΨ⟩ := τ
    have e : t (InfinitePlace.mk (τ.comp (algebraMap F E))) = τ := by
      rcases eq_or_conj c hτ h0 hcδ hs _ _ (mk_eq_iff (htw (InfinitePlace.mk (τ.comp (algebraMap F E))))) with e | e
      · exact e
      · exact absurd (e ▸ ht _) ((hΨ τ).1 hτΨ)
    have := hval τ a b
    simp only [ha, hb, e] at this
    refine this.trans ?_
    apply Complex.ext
    · rfl
    · exact div_mul_cancel₀ _ (him τ)

theorem infAdele_tensor_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → IsTotallyReal F → (∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); (∀ τ : E →+* ℂ, ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) ∧ ∀ θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ), (∀ τ, (∀ x, θ τ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ τ (a ⊗ₜ (1 : E))) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sg (InfiniteAdeleRing F) c z) = starRingEnd ℂ (θ τ z)) ∧ ∀ Ψ : Set (E →+* ℂ), (∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  intro F E _ _ _ _ _ c h2 hc hF hτ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  refine ⟨exists_hom, fun θ hθ => ?_⟩
  have hθ' := fun τ => hom_tmul τ (θ τ) (hθ τ).1 (hθ τ).2
  refine ⟨fun τ => ?_, fun τ z => ?_, bijective c h2 hc hτ θ hθ'⟩
  · exact IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing F) (θ τ) (hθ τ).2
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [sg, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id, hθ', map_mul, conj_ext]
      rw [← hτ]
      rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.InfAdeleCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NsmulIntegralMemNhdsZero
section
namespace GlobalTheory.IntegralNeighbourhoodZero

open IsDedekindDomain NumberField

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _

theorem nsmul_integral_mem_nhds_zero (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (RingOfIntegers F) F |
      ∃ a : FiniteAdeleRing (RingOfIntegers F) F,
        (∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F) ∧
          c = M • a} ∈ nhds (0 : FiniteAdeleRing (RingOfIntegers F) F) := by
  obtain ⟨m, hm⟩ : ∃ m : FiniteAdeleRing (RingOfIntegers F) F, m = algebraMap F _ ((M : F)⁻¹) := ⟨_, rfl⟩
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hmM : (M : FiniteAdeleRing (RingOfIntegers F) F) * m = 1 := by
    rw [hm, ← map_natCast (algebraMap F (FiniteAdeleRing (RingOfIntegers F) F)), ← map_mul,
      mul_inv_cancel₀ hMF, map_one]
  have hopen : IsOpen ((fun c => m * c) ⁻¹' {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F}) :=
    (isOpen_integral F).preimage (continuous_const.mul continuous_id)
  have h0 : (0 : FiniteAdeleRing (RingOfIntegers F) F) ∈ (fun c => m * c) ⁻¹'
      {a : FiniteAdeleRing (RingOfIntegers F) F |
        ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} := by
    intro v
    change (m * 0) v ∈ _
    rw [mul_zero]
    exact zero_mem _
  refine Filter.mem_of_superset (hopen.mem_nhds h0) ?_
  intro c hc
  refine ⟨m * c, hc, ?_⟩
  rw [nsmul_eq_mul, ← mul_assoc, hmM, one_mul]

end GlobalTheory.IntegralNeighbourhoodZero
end

