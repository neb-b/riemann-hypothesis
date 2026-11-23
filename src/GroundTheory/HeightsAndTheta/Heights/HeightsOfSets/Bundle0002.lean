module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseHeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem finitePlace_le_one_of_isIntegral {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {x : K} (hx : IsIntegral ℤ x) : v x ≤ 1 := by
  let y : 𝓞 K := ⟨x, hx⟩
  have h := FinitePlace.norm_le_one K v.maximalIdeal y
  rw [FinitePlace.norm_embedding_eq] at h
  exact h

theorem finsum_log_finitePlace_natCast {K : Type*} [Field K] [NumberField K] {δ : ℕ} (hδ : 0 < δ) :
    ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = -(Module.finrank ℚ K * Real.log δ) := by
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w (δ : K)).Finite :=
    FinitePlace.hasFiniteMulSupport hne
  have hprod := FinitePlace.prod_eq_inv_abs_norm hne
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun x hx ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hx))] at hprod
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [← Real.log_prod (fun v _ ↦ (map_ne_zero _).mpr hne), hprod]
    have : Algebra.norm ℚ ((δ : ℕ) : K) = (δ : ℚ) ^ (Module.finrank ℚ K) := by
      have := Algebra.norm_algebraMap (S := K) (δ : ℚ)
      simpa using this
    rw [this]
    push_cast
    rw [abs_pow, Nat.abs_cast, Real.log_inv, Real.log_pow]
  · intro v hv
    have h1' : v (δ : K) ≠ 1 := fun h ↦ hv (by show Real.log (v (δ : K)) = 0; rw [h, Real.log_one])
    exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')

theorem vectorL2Norm_le_sqrt_card_mul {m : ℕ} (w : Fin m → ℂ) {R : ℝ} (hR : 0 ≤ R) (hw : ∀ i, ‖w i‖ ≤ R) :
    l2Norm w ≤ Real.sqrt m * R := by
  rw [l2Norm, ← Real.sqrt_sq hR, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin m, R ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
    _ = m * R ^ 2 := by simp

theorem height_standard_le (z : Cone n (AlgebraicClosure ℚ)) (hz : BlockNonzero z) {δ : ℕ}
    (hδ : 0 < δ) {R : ℝ} (hR : 0 < R)
    (hint : ∀ k i, IsIntegral ℤ ((δ : AlgebraicClosure ℚ) * z k i))
    (harch : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) k i, ‖σ (z k i)‖ ≤ R) :
    height (HermLine.standard (n := n)) z ≤
      ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
  set K := coordField z
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd_def
  have hd : 0 < d := by rw [hd_def]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'

  have hloc : ∀ (v : FinitePlace K) (k : ι),
      Real.log (⨆ i, v (coordVec z k i)) ≤ -Real.log (v (δ : K)) := by
    intro v k
    have hδv : 0 < v (δ : K) := FinitePlace.pos_iff.mpr hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
    have hi0' : coordVec z k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
    have hpos : 0 < ⨆ i, v (coordVec z k i) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi0')
        (le_ciSup (f := fun i ↦ v (coordVec z k i)) (Set.finite_range _).bddAbove i0)
    rw [← Real.log_inv]
    refine Real.log_le_log hpos (ciSup_le fun i ↦ ?_)
    have hI : IsIntegral ℤ ((δ : K) * coordVec z k i) := by
      have h1 := hint k i
      have h2 : (K.val : K →+* AlgebraicClosure ℚ) ((δ : K) * coordVec z k i) =
          (δ : AlgebraicClosure ℚ) * z k i := by
        simp [coordVec]
      rw [← h2] at h1
      exact (isIntegral_algHom_iff ((K.val : K →+* AlgebraicClosure ℚ).toIntAlgHom)
        K.val.injective).mp h1
    have h3 := finitePlace_le_one_of_isIntegral v hI
    rw [map_mul] at h3
    calc v (coordVec z k i) = (v (δ : K))⁻¹ * (v (δ : K) * v (coordVec z k i)) := by
          field_simp
      _ ≤ (v (δ : K))⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hδv).le
      _ = (v (δ : K))⁻¹ := mul_one _
  have hsupp1 := finite_support_height (HermLine.standard (n := n)) z hz
  have hsupp2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (δ : K))).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hne).subset fun v hv h ↦ hv ?_
    have h' : v (δ : K) = 1 := h
    show Real.log (v (δ : K)) = 0
    rw [h', Real.log_one]
  set T := (hsupp1.union hsupp2).toFinset
  have hfin : (∑ᶠ v : FinitePlace K, ∑ k, ((HermLine.standard (n := n)).deg k : ℝ) *
      Real.log (⨆ i, v (coordVec z k i))) ≤ Fintype.card ι * (d * Real.log δ) := by
    rw [finsum_eq_sum_of_support_subset (s := T) _
      (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inl hv)))]
    have h2 : ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = ∑ v ∈ T, Real.log (v (δ : K)) :=
      finsum_eq_sum_of_support_subset (s := T) _
        (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inr hv)))
    have h3 := finsum_log_finitePlace_natCast (K := K) hδ
    rw [h2] at h3
    calc ∑ v ∈ T, ∑ k, ((HermLine.standard (n := n)).deg k : ℝ) * Real.log (⨆ i, v (coordVec z k i))
        ≤ ∑ v ∈ T, ∑ _k : ι, -Real.log (v (δ : K)) := by
          refine Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
          simp only [HermLine.standard, Int.cast_one, one_mul]
          exact hloc v k
      _ = Fintype.card ι * -(∑ v ∈ T, Real.log (v (δ : K))) := by
          simp [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = Fintype.card ι * (d * Real.log δ) := by rw [h3, neg_neg]

  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> rfl
  have : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have harchK : ∀ σ : K →+* ℂ, Real.log ((HermLine.standard (n := n)).metric
      fun k i ↦ σ (coordVec z k i)) ≤ ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    intro σ
    let σ' : AlgebraicClosure ℚ →+* ℂ := ComplexEmbedding.lift (AlgebraicClosure ℚ) σ
    have hσ : ∀ k i, σ (coordVec z k i) = σ' (z k i) := by
      intro k i
      have := ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure ℚ) σ (coordVec z k i)
      rw [← this]
      rfl
    have hpos : ∀ k, 0 < l2Norm (fun i ↦ σ (coordVec z k i)) := by
      intro k
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
      refine vectorL2Norm_pos (Function.ne_iff.mpr ⟨i0, ?_⟩)
      intro h
      apply hi0
      have h2 := (map_eq_zero σ).mp h
      have := congrArg Subtype.val h2
      simpa [coordVec] using this
    change Real.log (∏ k, l2Norm (fun i ↦ σ (coordVec z k i))) ≤ _
    rw [Real.log_prod (fun k _ ↦ (hpos k).ne')]
    refine Finset.sum_le_sum fun k _ ↦ Real.log_le_log (hpos k) ?_
    have := vectorL2Norm_le_sqrt_card_mul (fun i ↦ σ (coordVec z k i)) hR.le (fun i ↦ by rw [hσ]; exact harch σ' k i)
    simpa using this
  have harchSum : ∑ σ : K →+* ℂ, Real.log ((HermLine.standard (n := n)).metric
      fun k i ↦ σ (coordVec z k i)) ≤ d * ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    refine (Finset.sum_le_sum fun σ _ ↦ harchK σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]

  set S := ∑ k, Real.log (Real.sqrt (n k + 1) * R) with hS
  unfold height
  rw [← hd_def]
  calc d⁻¹ * (_ + _) ≤ d⁻¹ * (Fintype.card ι * (d * Real.log δ) +
        d * ∑ k, Real.log (Real.sqrt (n k + 1) * R)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfin harchSum) (inv_pos.mpr hd).le
    _ = ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hS]
        field_simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Module

noncomputable section

section Extension

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


open scoped Classical in
open Classical in
theorem card_embeddings_restrict (τ : K →+* ℂ) :
    (Finset.univ.filter fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L) = τ).card = finrank K L :=
  _root_.UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict τ

theorem sum_embeddings_restrict (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ f τ) (fun σ hσ ↦ by rw [(Finset.mem_filter.mp hσ).2]),
    Finset.sum_const, card_embeddings_restrict, nsmul_eq_mul]

theorem finprod_iSup_algebraMap_int {ι : Type*} [Finite ι] {y : ι → 𝓞 K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by
  set y' : ι → 𝓞 L := fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i) with hy'
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := by
    intro a b hab
    have h1 : algebraMap K L (a : K) = algebraMap K L (b : K) := congrArg (fun t : 𝓞 L ↦ (t : L)) hab
    exact RingOfIntegers.ext ((algebraMap K L).injective h1)
  have hy'0 : y' ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
  have hK := absNorm_mul_finprod_finitePlace_eq_one (K := K) hy
  have hL := absNorm_mul_finprod_finitePlace_eq_one (K := L) hy'0
  have hspan : Ideal.span (Set.range y') =
      (Ideal.span (Set.range y)).map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan, Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hL
  have hL' : ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y' i) := rfl
  rw [hL']
  set N : ℝ := ((Ideal.span (Set.range y)).absNorm : ℝ)
  have hN : N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hK
    exact zero_ne_one hK
  push_cast at hL
  rw [eq_inv_of_mul_eq_one_right hL, eq_inv_of_mul_eq_one_right hK, inv_pow]

theorem hasFiniteMulSupport_iSup_place {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) : Function.HasFiniteMulSupport fun w : FinitePlace F ↦ ⨆ i, w (y i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  have : Nonempty {j // y j ≠ 0} := ⟨⟨i0, hi0⟩⟩
  have h := Function.HasFiniteMulSupport.iSup (ι := {j // y j ≠ 0})
    (f := fun i (w : FinitePlace F) ↦ w (y i)) fun i ↦ FinitePlace.hasFiniteMulSupport i.2
  have e : (fun w : FinitePlace F ↦ ⨆ i, w (y i)) = fun w ↦ ⨆ i : {j // y j ≠ 0}, w (y i) :=
    funext fun w ↦ Finite.iSup_eq_iSup_subtype hy
  rw [e]
  exact h

theorem finprod_algebraMap {c : K} (hc : c ≠ 0) :
    ∏ᶠ w : FinitePlace L, w (algebraMap K L c) = (∏ᶠ v : FinitePlace K, v c) ^ finrank K L := by
  rw [FinitePlace.prod_eq_inv_abs_norm ((map_ne_zero _).mpr hc), FinitePlace.prod_eq_inv_abs_norm hc,
    ← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow]
  push_cast
  rw [abs_pow, inv_pow]

theorem finprod_iSup_algebraMap {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) y
  choose z hz using hint
  have hb0 : (b : K) ≠ 0 := by
    rw [Ne, RingOfIntegers.coe_eq_zero_iff]
    exact nonZeroDivisors.ne_zero hb
  have hzy : ∀ i, ((z i : 𝓞 K) : K) = (b : K) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine Function.ne_iff.mpr ⟨i, fun h ↦ hi ?_⟩
    have h1 : (b : K) * y i = 0 := by rw [← hzy i, h]; simp
    exact (mul_eq_zero.mp h1).resolve_left hb0
  have key := finprod_iSup_algebraMap_int (L := L) hz0
  have hsupK : ∀ v : FinitePlace K, ⨆ i, v (z i : K) = v (b : K) * ⨆ i, v (y i) := by
    intro v
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg v _) _).symm
  have hsupL : ∀ w : FinitePlace L, ⨆ i, w (algebraMap K L (z i : K)) =
      w (algebraMap K L (b : K)) * ⨆ i, w (algebraMap K L (y i)) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsupK, hsupL] at key
  have hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport ((map_ne_zero _).mpr hb0))
      (hasFiniteMulSupport_iSup_place hyL),
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hb0) (hasFiniteMulSupport_iSup_place hy),
    mul_pow, finprod_algebraMap hb0] at key
  have hne : (∏ᶠ v : FinitePlace K, v (b : K)) ^ finrank K L ≠ 0 := by
    rw [FinitePlace.prod_eq_inv_abs_norm hb0]
    simp [hb0]
  exact mul_left_cancel₀ hne key

theorem finsum_log_eq_log_finprod {α : Type*} {f : α → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : Function.HasFiniteMulSupport f) : ∑ᶠ a, Real.log (f a) = Real.log (∏ᶠ a, f a) := by
  have hf' : (Function.mulSupport f).Finite := hf
  have hs : Function.support (fun a ↦ Real.log (f a)) ⊆ hf'.toFinset := by
    intro a ha
    rw [Set.Finite.coe_toFinset]
    intro h1
    exact ha (by show Real.log (f a) = 0; rw [h1, Real.log_one])
  rw [finsum_eq_sum_of_support_subset _ hs,
    finprod_eq_prod_of_mulSupport_subset (s := hf'.toFinset) f (by rw [Set.Finite.coe_toFinset]),
    Real.log_prod fun a _ ↦ (hpos a).ne']

theorem iSup_place_pos {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι] {y : ι → F}
    (hy : y ≠ 0) (w : FinitePlace F) : 0 < ⨆ i, w (y i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  exact lt_of_lt_of_le ((FinitePlace.pos_iff (w := w)).mpr hi0)
    (le_ciSup (f := fun i ↦ w (y i)) (Set.finite_range _).bddAbove i0)

theorem finsum_log_iSup_algebraMap {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ i, w (algebraMap K L (y i))) =
      finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (y i)) := by
  have hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  rw [finsum_log_eq_log_finprod (iSup_place_pos hyL) (hasFiniteMulSupport_iSup_place hyL),
    finsum_log_eq_log_finprod (iSup_place_pos hy) (hasFiniteMulSupport_iSup_place hy),
    finprod_iSup_algebraMap hy, Real.log_pow]

end Extension

theorem finsum_sum_mul {α ι : Type*} [Fintype ι] (c : ι → ℝ) (g : ι → α → ℝ)
    (hg : ∀ k, (Function.support (g k)).Finite) :
    ∑ᶠ a, ∑ k, c k * g k a = ∑ k, c k * ∑ᶠ a, g k a := by
  have hS : (⋃ k, Function.support (g k)).Finite := Set.finite_iUnion hg
  have hsub : ∀ k, Function.support (g k) ⊆ hS.toFinset := fun k ↦ by
    rw [Set.Finite.coe_toFinset]
    exact Set.subset_iUnion (fun k ↦ Function.support (g k)) k
  have hsum : Function.support (fun a ↦ ∑ k, c k * g k a) ⊆ hS.toFinset := by
    intro a ha
    rw [Set.Finite.coe_toFinset, Set.mem_iUnion]
    by_contra h
    push Not at h
    exact ha (Finset.sum_eq_zero fun k _ ↦ by rw [Function.notMem_support.mp (h k), mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [finsum_eq_sum_of_support_subset _ (hsub k), Finset.mul_sum]

theorem support_log_iSup_place_finite {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) :
    (Function.support fun w : FinitePlace F ↦ Real.log (⨆ i, w (y i))).Finite := by
  refine Set.Finite.subset (hasFiniteMulSupport_iSup_place hy) fun w hw h1 ↦ hw ?_
  have h1' : (⨆ i, w (y i)) = 1 := h1
  change Real.log (⨆ i, w (y i)) = 0
  rw [h1', Real.log_one]

section Cone

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}



end Cone

end

end GroundTheory.Heights₂.Heights
end

