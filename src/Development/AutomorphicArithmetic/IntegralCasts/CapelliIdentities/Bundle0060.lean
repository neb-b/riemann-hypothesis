module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumEmbeddingsEqRealAddComplex
section
namespace UpperTheory.Reformulated.B.DYhb7

open NumberField NumberField.InfinitePlace Finset

private lemma algebra_trace_pi_eq_sum_trace {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    [Module.Free ℝ A] [Module.Finite ℝ A] (x : ι → A) :
    Algebra.trace ℝ (ι → A) x = ∑ i, Algebra.trace ℝ A (x i) := by
  classical
  let b := Module.Free.chooseBasis ℝ A
  let B := Pi.basis (fun _ : ι => b)
  rw [Algebra.trace_eq_matrix_trace B]
  simp_rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.diag_apply,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  simp [B, Pi.basis_apply, Pi.basis_repr, Pi.mul_apply]

open scoped Classical in
private lemma fiber_embeddings_eq_pair {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    ({φ | mk φ = w} : Finset (F →+* ℂ)) = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  conv_lhs => rw [← mk_embedding w, mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h]; simp [ComplexEmbedding.conjugate])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; simp [ComplexEmbedding.conjugate])

open scoped Classical in
private lemma sum_embeddings_eq_real_add_complex {F : Type} [Field F] [NumberField F] (y : F) :
    ∑ φ : F →+* ℂ, φ y =
      (∑ w : {w : InfinitePlace F // IsReal w}, (embedding_of_isReal w.2 y : ℂ)) +
      ∑ w : {w : InfinitePlace F // IsComplex w}, (((2 * (w.1.embedding y).re : ℝ)) : ℂ) := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => mk φ), sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, conjugate_embedding_eq_of_isReal w.2]
    simp
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, Finset.sum_pair]
    · rw [ComplexEmbedding.conjugate_coe_eq]
      push_cast
      rw [Complex.add_conj]
      push_cast
      rfl
    · intro h
      exact (isComplex_iff.mp w.2) (ComplexEmbedding.isReal_iff.mpr h.symm)

end UpperTheory.Reformulated.B.DYhb7

theorem UpperTheory.Reformulated.B.DYhb7.main :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
      (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
          ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
        (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by
  intro F _ _ y
  classical
  apply Complex.ofReal_injective
  have h1 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ y := by
    have := _root_.trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f y) _ fun _ => by
      simp [RingHom.equivRatAlgHom_apply]).symm
  rw [Complex.ofReal_ratCast, h1, UpperTheory.Reformulated.B.DYhb7.sum_embeddings_eq_real_add_complex, Algebra.trace_prod_apply,
    UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace, UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace]
  simp [Algebra.trace_complex_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRightInverse
section
theorem UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulLeftInvariant] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      (μ : Set G → ENNReal) (↑K : Set G) ≠ ⊤ →
        ∀ {S : Set G},
          IsCompact S →
            (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
              ∃ (t : Finset (G ⧸ K)),
                (∀ Q ∈ t, Quotient.out Q ∈ S) ∧
                  ∀ (f : G → ℂ),
                    (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
                      ∫ (g : G) in S, f g ∂μ = ∑ Q ∈ t, f (Quotient.out Q) * (↑(μ.real (↑K : Set G)) : ℂ) := by
  intro G _ _ _ _ _ μ _ K hK hμ S hS hSK
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  let C : G ⧸ K → Set G := fun Q => (fun g => (Quotient.out Q)⁻¹ * g) ⁻¹' (K : Set G)
  have hC : ∀ Q g, g ∈ C Q ↔ (QuotientGroup.mk g : G ⧸ K) = Q := by
    intro Q g
    have h := QuotientGroup.eq (s := K) (a := Quotient.out Q) (b := g)
    rw [QuotientGroup.out_eq'] at h
    rw [eq_comm, h]
    rfl
  have hout : ∀ Q ∈ hfin.toFinset, Quotient.out Q ∈ S := by
    intro Q hQ
    obtain ⟨s, hs, rfl⟩ := hfin.mem_toFinset.1 hQ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hk]
    exact hSK s hs k k.2
  have hmeas : ∀ Q, MeasurableSet (C Q) := fun Q =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ Q, μ (C Q) = μ K := fun Q => MeasureTheory.measure_preimage_mul μ _ _
  have hU : S = ⋃ Q ∈ hfin.toFinset, C Q := by
    ext g
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hg
      exact ⟨_, hfin.mem_toFinset.2 ⟨g, hg, rfl⟩, (hC _ g).2 rfl⟩
    · rintro ⟨Q, hQ, hg⟩
      have := hSK _ (hout Q hQ) _ hg
      simpa using this
  refine ⟨hfin.toFinset, hout, fun f hf => ?_⟩
  have hconst : ∀ Q ∈ hfin.toFinset, Set.EqOn f (fun _ => f (Quotient.out Q)) (C Q) := by
    intro Q hQ g hg
    have := hf _ (hout Q hQ) _ hg
    simpa using this
  have hsplit : ∫ g in ⋃ Q ∈ hfin.toFinset, C Q, f g ∂μ
      = ∑ Q ∈ hfin.toFinset, ∫ g in C Q, f g ∂μ := by
    refine MeasureTheory.integral_biUnion_finset _ (fun Q _ => hmeas Q) ?_ ?_
    · intro Q _ R _ hQR
      refine Set.disjoint_left.2 fun g h1 h2 => hQR ?_
      rw [← (hC Q g).1 h1, (hC R g).1 h2]
    · intro Q hQ
      refine (MeasureTheory.integrableOn_congr_fun (hconst Q hQ) (hmeas Q)).2 ?_
      exact MeasureTheory.integrableOn_const (by rw [hμC]; exact hμ)
  rw [← hU] at hsplit
  rw [hsplit]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [MeasureTheory.setIntegral_congr_fun (hmeas Q) (hconst Q hQ),
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, hμC,
    MeasureTheory.measureReal_def, Complex.real_smul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableAbsNormRpowInv
section
open Filter Asymptotics NumberField

private theorem UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO (K : Type*) [Field K] [NumberField K] :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  have hlim := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
  have hO : (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ))
      =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
    refine isBigO_of_div_tendsto_nhds ?_ _ hlim
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd (Nat.cast_eq_zero.mp h) hn
  simp only [Real.rpow_one]
  refine IsBigO.trans (isBigO_of_le _ fun n ↦ ?_) hO
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)
      ≤ ∑ k ∈ Finset.Icc 0 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left zero_le_one)
          fun _ _ _ ↦ by positivity
    _ = _ := by
        rw [← Nat.cast_sum, ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
        simp [Set.coe_eq_subtype]

private theorem UpperTheory.Reformulated.B.Qp7.summable_count_mul (K : Type*) [Field K] [NumberField K] {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ σ)⁻¹ := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (σ : ℂ))
    (UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO K) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (by simpa using hσ)
  refine h.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (zero_lt_one.trans hσ).ne']
  · simp [div_eq_mul_inv]

theorem UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {σ : ℝ},
    (1 : ℝ) < σ →
      Summable fun (I : Ideal (NumberField.RingOfIntegers K)) ↦
        ((↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) I) : ℝ) ^ σ)⁻¹ := by
  intro K _ _ σ hσ
  have hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    fun n ↦ (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ ↦ by simp only [Function.comp_apply]; positivity)]
  refine ⟨fun n ↦ Summable.of_finite, ?_⟩
  refine (UpperTheory.Reformulated.B.Qp7.summable_count_mul K hσ).congr fun n ↦ ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((Ideal.absNorm I.1 : ℝ) ^ σ)⁻¹ = ((n : ℝ) ^ σ)⁻¹ := fun I ↦ by rw [I.2]
  simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, this, tsum_const, nsmul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord
section
private lemma sum_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hs : Summable g) (s : Finset (ι → α)) :
    ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∏ _i : ι, ∑' x, g x := by
  haveI : DecidableEq α := Classical.decEq α
  let t : ι → Finset α := fun i => s.image fun η : ι → α => η i
  have hsub : s ⊆ Fintype.piFinset t := by
    intro ξ hξ
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.2 ⟨ξ, hξ, rfl⟩
  have h1 : ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun ξ _ _ => Finset.prod_nonneg fun i _ => hg (ξ i)
  have h2 : ∏ i, ∑ x ∈ t i, g x = ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.prod_univ_sum t fun _ x => g x
  have h3 : ∏ i, ∑ x ∈ t i, g x ≤ ∏ _i : ι, ∑' x, g x := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.sum_nonneg fun x _ => hg x
    · intro i _
      exact hs.sum_le_tsum (t i) fun x _ => hg x
  exact h1.trans (h2.symm.le.trans h3)

theorem UpperTheory.Reformulated.B.Qo1.summable_prod_coord.{u_2, u_3} :
    ∀ {ι : Type u_2} [inst : Fintype ι] [DecidableEq ι] {α : Type u_3} {g : α → ℝ},
    (∀ (x : α), (0 : ℝ) ≤ g x) → Summable g → Summable fun (ξ : ι → α) ↦ ∏ i : ι, g (ξ i) := by
  intro ι _ _ α g hg hs
  have h0 : ∀ ξ : ι → α, 0 ≤ ∏ i, g (ξ i) := fun ξ => Finset.prod_nonneg fun i _ => hg (ξ i)
  exact summable_of_sum_le h0 (sum_prod_le hg hs)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummandLocalization
section
theorem UpperTheory.Reformulated.B.SummandLocalization.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)

theorem UpperTheory.Reformulated.B.SummandLocalization.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.SummandLocalization.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.SummandLocalization.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locF :
    {K F W : Type} →
      [inst : Field K] →
        [inst_1 : Field F] →
          [Algebra F K] →
            [inst_3 : AddCommGroup W] →
              [inst_4 : _root_.Module (NumberField.RingOfIntegers K) W] →
                Ideal (NumberField.RingOfIntegers F) →
                  Submodule (NumberField.RingOfIntegers K) W → Submodule (NumberField.RingOfIntegers K) W :=
    fun {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [_root_.Module (NumberField.RingOfIntegers K) W]
        (𝔭 : Ideal (NumberField.RingOfIntegers F)) (L : Submodule (NumberField.RingOfIntegers K) W) ↦
      UpperTheory.Reformulated.B.SummandLocalization.locS
        (Submonoid.closure
          {s : NumberField.RingOfIntegers K |
            ∃ t ∉ 𝔭,
              (Algebra.algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) :
                    NumberField.RingOfIntegers F → NumberField.RingOfIntegers K)
                  t =
                s})
        L

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.SummandLoc :
    Prop :=
    ∀ (K F V : Type) [inst : Field K] [NumberField K] [inst_2 : Field F] [NumberField F] [inst_4 : Algebra F K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [FiniteDimensional K V]
      [inst_8 : _root_.Module (NumberField.RingOfIntegers K) V] [inst_9 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      (X : Submodule K V) (𝔭 : Ideal (NumberField.RingOfIntegers F)),
      𝔭.IsMaximal →
        ∀ (Λ : Submodule (NumberField.RingOfIntegers K) V),
          (∃ (Λ₀ : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsFullLattice K Λ₀ ∧ UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 Λ₀ = Λ) →
            ∃ (π : V →ₗ[K] V), (∀ (v : V), (π : V → V) v ∈ X) ∧ (∀ x ∈ X, (π : V → V) x = x) ∧ ∀ y ∈ Λ, (π : V → V) y ∈ Λ

private theorem UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule {R K W : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (M : Submodule R W) (hM : Submodule.span K (M : Set W) = ⊤) :
    IsLocalizedModule (nonZeroDivisors R) M.subtype where
  map_units s := by
    have hs : algebraMap R K s ≠ 0 := (IsLocalization.map_units K s).ne_zero
    rw [Module.End.isUnit_iff]
    have h : ((algebraMap R (Module.End R W)) s : W → W) = fun w => (algebraMap R K s) • w := by
      funext w
      simp
    rw [h]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj y := by
    have hy : y ∈ Submodule.span K (M : Set W) := hM ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set W) y hy
    rw [Submodule.span_eq] at ht
    exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

private theorem UpperTheory.Reformulated.B.SummandLocalization.exists_proj {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (X : Submodule K V) (L : Submodule R V) (hL : Submodule.IsFullLattice K L) :
    ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ L, π y ∈ L := by
  let q : V →ₗ[R] V ⧸ X := X.mkQ.restrictScalars R
  let M : Submodule R (V ⧸ X) := L.map q
  have hM : Submodule.span K (M : Set (V ⧸ X)) = ⊤ := by
    have h : (M : Set (V ⧸ X)) = X.mkQ '' (L : Set V) := rfl
    rw [h, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 (hL.fg.map q)
  haveI : Module.IsTorsionFree R (V ⧸ X) := Module.IsTorsionFree.trans_faithfulSMul R K (V ⧸ X)
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  haveI : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  have hsurj : Function.Surjective (q.submoduleMap L) := LinearMap.submoduleMap_surjective q L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (q.submoduleMap L) LinearMap.id hsurj
  haveI := UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule M hM
  have hb : IsBaseChange K M.subtype := IsLocalizedModule.isBaseChange (nonZeroDivisors R) K M.subtype
  let σ : (V ⧸ X) →ₗ[K] V := hb.lift (L.subtype ∘ₗ s)
  have hσ : ∀ m : M, σ m = (s m : V) := fun m => hb.lift_eq (L.subtype ∘ₗ s) m
  have hq : X.mkQ ∘ₗ σ = LinearMap.id := by
    apply LinearMap.ext_on hM
    intro m hm
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨m, hm⟩)
    rw [LinearMap.comp_apply, hσ ⟨m, hm⟩]
    exact h1
  refine ⟨LinearMap.id - σ ∘ₗ X.mkQ, fun v => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 := LinearMap.congr_fun hq (X.mkQ v)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  · have h1 : X.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero X).2 hx
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  · have h1 := hσ ⟨q y, Submodule.mem_map_of_mem hy⟩
    have h2 : σ (X.mkQ y) ∈ L := by
      have h3 : σ (X.mkQ y) = _ := h1
      rw [h3]
      exact Subtype.property _
    exact L.sub_mem hy h2

theorem UpperTheory.Reformulated.B.SummandLocalization.summand_localization :
    UpperTheory.Reformulated.B.SummandLocalization.SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 _ Λ ⟨Λ₀, hΛ₀, rfl⟩
  obtain ⟨π, h1, h2, h3⟩ := UpperTheory.Reformulated.B.SummandLocalization.exists_proj X Λ₀ hΛ₀
  refine ⟨π, h1, h2, ?_⟩
  rintro y ⟨s, hs, hy⟩
  refine ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower]
  exact h3 _ hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SxLimPt
section
theorem UpperTheory.Reformulated.B.Qg4.sxLimPt :
    ∀ {Λ A R S : Type} [inst : CommRing Λ] [inst_1 : CommRing A] [inst_2 : Algebra Λ A]
    [inst_3 : CommRing R] [inst_4 : Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R),
    (∀ (N : ℕ),
        ∃ (f : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          ∀ (s : S),
            (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) =
              (Ideal.Quotient.mk (I ^ (N + (1 : ℕ))) : R → R ⧸ I ^ (N + (1 : ℕ))) (y s)) →
      (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          (∀ (s : S), (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) = (f' : A → R ⧸ I ^ (N + (1 : ℕ))) (e s)) → f = f') →
        ∃ (f : A →ₐ[Λ] R), ∀ (s : S), (f : A → R) (e s) = y s := by
  intro Λ A R S _ _ _ _ _ I _ e y hex huniq
  choose f hf using hex
  have hc : ∀ {m n : ℕ} (hle : m + 1 ≤ n + 1),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    refine huniq m _ _ fun s => ?_
    rw [AlgHom.comp_apply, hf, hf]
    rfl
  let g : (n : ℕ) → A →ₐ[Λ] R ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (f n)
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (g n) = g m := by
    intro m n hle
    refine AlgHom.ext fun a => ?_
    simp only [g, ← hc (Nat.succ_le_succ hle), AlgHom.comp_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f n a)
    rw [← hr]
    rfl
  refine ⟨IsAdicComplete.liftAlgHom I g hg, fun s => ?_⟩
  have key : (fun s => IsAdicComplete.liftAlgHom I g hg (e s)) = y := by
    apply IsHausdorff.funext' I
    intro n t
    have h1 := IsAdicComplete.mk_liftAlgHom I g hg n (e t)
    refine h1.trans ?_
    simp only [g, AlgHom.comp_apply, hf]
    rfl
  exact congrFun key s
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubRight
section
theorem UpperTheory.Reformulated.B.Qn17.tensor_sub_right.{u} :
    ∀ {R : Type} [inst : CommRing R] (M N : Type u) [inst_1 : AddCommMonoid M]
    [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M] [inst_4 : _root_.Module R N] [Subsingleton N],
    Subsingleton (TensorProduct R M N) := by
  intro R _ M N _ _ _ _ _
  have h : ∀ x : TensorProduct R M N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TmulSurjectiveRankOne
section
theorem UpperTheory.Reformulated.B.Qj4.tmul_surjective_rank_one :
    ∀ {O T X : Type} [inst : CommRing O]
    [inst_1 : AddCommGroup T] [inst_2 : _root_.Module O T] [inst_3 : AddCommGroup X] [inst_4 : _root_.Module O X]
    (x₀ : X), (∀ (x : X), ∃ (c : O), x = c • x₀) → ∀ (m : TensorProduct O T X), ∃ (t : T), t ⊗ₜ[O] x₀ = m := by
  intro O T X _ _ _ _ _ x₀ h m
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.zero_tmul T x₀⟩
  | tmul t x =>
    obtain ⟨c, rfl⟩ := h x
    exact ⟨c • t, TensorProduct.smul_tmul c t x₀⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, TensorProduct.add_tmul s t x₀⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TraceMixedEmbedding
section
theorem UpperTheory.Reformulated.B.TraceMixedEmbedding.trace_mixedEmbedding :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
    (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
        ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
      (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by
  intro F _ _ y
  classical
  rw [Algebra.trace_eq_matrix_trace (NumberField.mixedEmbedding.latticeBasis F),
    Algebra.trace_eq_matrix_trace (NumberField.integralBasis F)]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [NumberField.mixedEmbedding.latticeBasis_apply, ← map_mul,
    NumberField.mixedEmbedding.latticeBasis_repr_apply]
end

