module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IntermediateField.algebraAdjoinAdjoin

noncomputable section


set_option maxHeartbeats 400000 in
theorem SpanBundleTrdegLe.proof : SpanBundleTrdegLe.Statement := by
  intro F _ Ω _ _ K _ ι y M i G c a H _hc hH hGH Φ _ _ s

  let κΦ : Φ →+* FractionRing (MvPolynomial (Option K) Φ) :=
    (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp C
  let κ : Ω →+* FractionRing (MvPolynomial (Option K) Φ) := κΦ.comp (algebraMap Ω Φ)
  let _ : Algebra F (FractionRing (MvPolynomial (Option K) Φ)) := (κ.comp (algebraMap F Ω)).toAlgebra
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))) :=
    IsFractionRing.injective _ _
  let Xo : Option K → FractionRing (MvPolynomial (Option K) Φ) := fun o =>
    algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ)) (X o)

  let gy : (Σ k, ι k) → FractionRing (MvPolynomial (Option K) Φ) := fun p => κ (y p) * Xo (some p.1)

  have hAy : Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) ≤
      Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) := by
    have hθ : ∀ f, (aeval gy : MRing ι F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) f =
        algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
          (rename some (map (algebraMap Ω Φ) (pointConeMap F y f))) := by
      intro f
      have e := MvPolynomial.ringHom_ext
        (f := ((aeval gy : MRing ι F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
          MRing ι F →+* FractionRing (MvPolynomial (Option K) Φ)))
        (g := ((algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp
          (((rename some : MvPolynomial K Φ →ₐ[Φ] MvPolynomial (Option K) Φ) :
            MvPolynomial K Φ →+* MvPolynomial (Option K) Φ).comp
            ((map (algebraMap Ω Φ)).comp (pointConeMap F y : MRing ι F →+* MvPolynomial K Ω)))))
        (fun r => by
          simp [pointConeMap, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra, κ, κΦ])
        (fun p => by simp [pointConeMap, gy, κ, κΦ, Xo])
      exact congrArg (fun φ => φ f) e
    rw [Algebra.adjoin_range_eq_range_aeval]
    refine trdeg_le_of_surjective (Ideal.Quotient.liftₐ (pointIdeal F y) (aeval gy).rangeRestrict ?_) ?_
    · intro f hf
      apply Subtype.ext
      change (aeval gy) f = 0
      rw [hθ, show pointConeMap F y f = 0 from hf]
      simp
    · intro x
      obtain ⟨f, rfl⟩ := AlgHom.rangeRestrict_surjective _ x
      exact ⟨Ideal.Quotient.mk _ f, rfl⟩

  have hSyL : Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) =
      Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) := by
    have : FaithfulSMul F (Algebra.adjoin F (Set.range gy)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have : FaithfulSMul F (IntermediateField.adjoin F (Set.range gy)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have e := trdeg_add_eq F (Algebra.adjoin F (Set.range gy))
      (A := IntermediateField.adjoin F (Set.range gy))
    rwa [trdeg_eq_zero (R := Algebra.adjoin F (Set.range gy)), add_zero] at e

  have hchart : ∀ u ∈ chartRing F (segreVec y) c, κ u ∈ IntermediateField.adjoin F (Set.range gy) := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem u hu =>
      obtain ⟨c', rfl⟩ := hu
      have hQ : ∏ k, Xo (some k) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => (map_ne_zero_iff _ hinj).2 (X_ne_zero _)
      have e : κ (segreVec y c' / segreVec y c) = (∏ k, gy ⟨k, c' k⟩) / ∏ k, gy ⟨k, c k⟩ := by
        simp only [gy, Finset.prod_mul_distrib, segreVec, map_div₀, map_prod]
        rw [mul_div_mul_right _ _ hQ]
      rw [e]
      exact div_mem (prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)
        (prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)
    | algebraMap r => exact IntermediateField.algebraMap_mem _ r
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | mul u v _ _ hu hv => rw [map_mul]; exact mul_mem hu hv

  choose g hg hGm using hGH
  set p0 : Ω := ∏ k, y ⟨k, c k⟩ ^ a k with hp0
  have hgL : ∀ l m, κ (g l m) ∈ IntermediateField.adjoin F (Set.range gy) := fun l m => hchart _ (hg l m)

  let w : Fin i → FractionRing (MvPolynomial (Option K) Φ) := fun m =>
    κ p0 * κΦ (∑ m', algebraMap Ω Φ (H⁻¹ m m') * s m') * Xo none
  let T := (aeval w : MvPolynomial (Fin i) (IntermediateField.adjoin F (Set.range gy)) →ₐ[_]
    FractionRing (MvPolynomial (Option K) Φ)).range
  have hTi : Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T ≤ i := by
    have := trdeg_le_of_surjective _ (AlgHom.rangeRestrict_surjective
      (aeval w : MvPolynomial (Fin i) (IntermediateField.adjoin F (Set.range gy)) →ₐ[_]
        FractionRing (MvPolynomial (Option K) Φ)))
    simpa using this
  have : FaithfulSMul F (IntermediateField.adjoin F (Set.range gy)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul (IntermediateField.adjoin F (Set.range gy)) T :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have hT : Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) +
      Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T = Algebra.trdeg F T :=
    trdeg_add_eq F (IntermediateField.adjoin F (Set.range gy)) (A := T)

  let gz : (Σ o, bundleIdx ι M o) → FractionRing (MvPolynomial (Option K) Φ) := fun p =>
    algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
      (C (projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) *
        X p.1)
  have hφ : ∀ l m', ((LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (Pi.basisFun Ω (Fin i) m') : Ω) =
      G l m' := by
    intro l m'
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hΦ : ∀ l, (∑ m', s m' * algebraMap Ω Φ (G l m')) =
      ∑ m, algebraMap Ω Φ (g l m) * algebraMap Ω Φ p0 * ∑ m', algebraMap Ω Φ (H⁻¹ m m') * s m' := by
    intro l
    have hG : ∀ m', G l m' = ∑ m, (g l m * p0) * H⁻¹ m m' := by
      intro m'
      have h := congrFun (congrFun (Matrix.mul_nonsing_inv_cancel_right H (Matrix.of G) hH) l) m'
      rw [Matrix.mul_apply] at h
      calc G l m' = Matrix.of G l m' := rfl
        _ = _ := h.symm
        _ = _ := Finset.sum_congr rfl fun m _ => by rw [hGm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hG, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
  have hnone : ∀ l : Fin M, gz ⟨none, l⟩ = ∑ m, κ (g l m) * w m := by
    intro l
    have e1 : projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s
        (⟨none, l⟩ : Σ o, bundleIdx ι M o) = ∑ m', s m' * algebraMap Ω Φ (G l m') := by
      simp only [projCoord, hφ]
    have e2 : gz ⟨none, l⟩ = κΦ (∑ m', s m' * algebraMap Ω Φ (G l m')) * Xo none := by
      simp only [gz, e1, map_mul]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, hΦ l, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [w, κ, RingHom.comp_apply, map_mul]
    ring
  have hsome : ∀ k (j : ι k), gz ⟨some k, j⟩ = gy ⟨k, j⟩ := by
    intro k j
    simp only [gz, gy, projCoord, map_mul]
    rfl
  have hgzT : ∀ p, gz p ∈ T := by
    rintro ⟨_ | k, j⟩
    · rw [hnone j]
      refine ⟨∑ m, C ⟨κ (g j m), hgL j m⟩ * X m, ?_⟩
      set_option synthInstance.maxHeartbeats 200000 in
        simp
    · rw [hsome k j]
      exact ⟨C ⟨gy ⟨k, j⟩, IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩⟩, by simp⟩

  have hz : ∀ f, (aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) f =
      algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
        (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
          (fun p => C (projCoord y (Pi.basisFun Ω (Fin i))
            (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) * X p.1) f) := by
    intro f
    have e := MvPolynomial.ringHom_ext
      (f := ((aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
        MRing (bundleIdx ι M) F →+* FractionRing (MvPolynomial (Option K) Φ)))
      (g := (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp
        (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
          (fun p => C (projCoord y (Pi.basisFun Ω (Fin i))
            (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) * X p.1)))
      (fun r => by simp [RingHom.algebraMap_toAlgebra, κ, κΦ])
      (fun p => by simp [gz])
    exact congrArg (fun φ => φ f) e
  let φT : MRing (bundleIdx ι M) F →ₐ[F] T := aeval fun p => ⟨gz p, hgzT p⟩
  have hφT : ∀ f, (φT f : FractionRing (MvPolynomial (Option K) Φ)) = aeval gz f := by
    intro f
    have e := MvPolynomial.ringHom_ext
      (f := (T.val : T →+* FractionRing (MvPolynomial (Option K) Φ)).comp
        (φT : MRing (bundleIdx ι M) F →+* T))
      (g := ((aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
        MRing (bundleIdx ι M) F →+* FractionRing (MvPolynomial (Option K) Φ)))
      (fun r => by simp [φT])
      (fun p => by simp [φT])
    exact congrArg (fun φ => φ f) e
  have hmem : ∀ f, φT f = 0 ↔ f ∈ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s := by
    intro f
    rw [projIdeal, RingHom.mem_ker, ← Subtype.val_inj, hφT, hz, ZeroMemClass.coe_zero,
      map_eq_zero_iff _ hinj]
  have hAz : Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ≤ Algebra.trdeg F T := by
    refine trdeg_le_of_injective (Ideal.Quotient.liftₐ _ φT fun f hf => (hmem f).2 hf) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hmem f).1 hx)
  calc _ ≤ Algebra.trdeg F T := hAz
    _ = Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) +
        Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T := hT.symm
    _ ≤ Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) + i := by gcongr
    _ = Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) + i := by rw [hSyL]
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinDivDiffExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace dividedDifferenceExpansion

theorem prod_split {M : Type*} [CommMonoid M] {r : ℕ} (l : Fin r) (f : Fin r → M) :
    ∏ j, f j = (∏ j ∈ Finset.univ.filter (fun j => j < l), f j) * f l *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), f j := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j < l),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l),
    Finset.filter_filter, Finset.filter_filter, mul_assoc]
  congr 2
  · rw [Finset.prod_eq_single l]
    · intro b hb hbl
      simp only [Finset.mem_filter] at hb
      exact absurd hb.2.2 hbl
    · intro h
      exact absurd (by simp) h
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    · intro h
      exact ⟨not_lt.mpr h.le, ne_of_gt h⟩

noncomputable def stair {r : ℕ} (μ : Fin r →₀ ℕ) (k : ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  ∏ j : Fin r, X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) ^ μ j

theorem stair_zero {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ 0 = ∏ j, X (Sum.inl j) ^ μ j := by
  simp [stair]

theorem stair_top {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ r = ∏ j, X (Sum.inr j) ^ μ j := by
  simp [stair]

theorem term_eq {r : ℕ} (μ : Fin r →₀ ℕ) (l : Fin r) :
    (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      stair μ l - stair μ (l + 1) := by
  have hg : (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) =
      X (Sum.inl l) ^ μ l - X (Sum.inr l) ^ μ l := by
    rw [mul_comm]
    exact geom_sum₂_mul _ _ _
  have hlo : ∀ k : ℕ, (l : ℕ) ≤ k →
      ∏ j ∈ Finset.univ.filter (fun j => j < l),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (j : ℕ) < l := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_pos (by omega)]
  have hhi : ∀ k : ℕ, k ≤ (l : ℕ) + 1 →
      ∏ j ∈ Finset.univ.filter (fun j => l < j),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (l : ℕ) < j := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_neg (by omega)]
  unfold stair
  rw [prod_split l, prod_split l (fun j => (X (if (j : ℕ) < (l : ℕ) + 1 then Sum.inr j else Sum.inl j) :
      MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j), hlo l le_rfl, hlo (l + 1) (by omega),
    hhi l (by omega), hhi (l + 1) le_rfl, if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
  linear_combination
    ((∏ j ∈ Finset.univ.filter (fun j => j < l), (X (Sum.inr j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j) *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) * hg

theorem sum_term_eq {r : ℕ} (μ : Fin r →₀ ℕ) :
    ∑ l : Fin r, (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      ∏ j, X (Sum.inl j) ^ μ j - ∏ j, X (Sum.inr j) ^ μ j := by
  simp_rw [term_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i => stair μ i - stair μ (i + 1)) r,
    Finset.sum_range_sub', stair_zero, stair_top]

theorem rename_eq_sum {r : ℕ} (f : Fin r → Fin r ⊕ Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename f G = ∑ μ ∈ G.support, C (G.coeff μ) * ∏ j, X (f j) ^ μ j := by
  conv_lhs => rw [G.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), map_mul, rename_C, map_prod]
  simp [map_pow, rename_X]

theorem rename_divDiff {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ G.support, C (G.coeff μ) *
        ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
          (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
          ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem proof : dividedDifferenceExpansion.Statement := by
  intro r m G hG
  refine ⟨?_, ?_⟩
  · rw [rename_eq_sum, rename_eq_sum, ← Finset.sum_sub_distrib]
    calc ∑ μ ∈ G.support, (C (G.coeff μ) * ∏ j, X (Sum.inl j) ^ μ j -
            C (G.coeff μ) * ∏ j, X (Sum.inr j) ^ μ j)
        = ∑ μ ∈ G.support, ∑ l : Fin r, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_congr rfl fun μ _ => by rw [← Finset.mul_sum, sum_term_eq, mul_sub]
      _ = ∑ l : Fin r, ∑ μ ∈ G.support, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => by
          rw [rename_divDiff, Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
  · intro l
    rcases m with _ | d
    · have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G = 0 := by
        unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
        refine Finset.sum_eq_zero fun μ hμ => ?_
        have h := hG (mem_support_iff.mp hμ)
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
        have hl : μ l = 0 := by
          have h' : ∑ j, μ j = 0 := by simpa using h
          exact (Finset.sum_eq_zero_iff.mp h') l (Finset.mem_univ l)
        simp [hl]
      rw [h0, map_zero]
      exact isHomogeneous_zero _ _ _
    · simpa using (BundleExamples.isHomogeneous_divDiff l hG).rename_isHomogeneous
        (f := finSumFinEquiv.symm)

end dividedDifferenceExpansion

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointVertDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)

noncomputable section

namespace JoinPointVerticalDivisor

variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem rename_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') h ∈ mcIdeal R (joinCoord y z) ↔ h ∈ mcIdeal R y := by
  rw [← BundleExamples.joinCoords_eq, ← BundleExamples.joinForm_eq]
  exact joinForm_mem_pointIdeal_iff R y z h

theorem isMultiHomog_rename {R : Type} [CommRing R] {f : MvPolynomial (Σ k, ι k) R} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (liftVar ι') f) (Sum.elim a 0) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_joinForm hf


omit [Fintype K'] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] {R : Type} [CommRing R]
    (b : K → ℕ) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') (weightedHomogeneousComponent (blockWeight ι) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) (Sum.elim b 0)
        (rename (liftVar ι') h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MRing ι R) (Finsupp.weight (blockWeight ι) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have hj : IsMultiHomog (rename (liftVar ι') (monomial d r : MRing ι R))
        (Sum.elim (Finsupp.weight (blockWeight ι) d) 0) := isMultiHomog_joinForm hm
    by_cases hb : b = Finsupp.weight (blockWeight ι) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · have hb' : (Sum.elim b 0 : K ⊕ K' → ℕ) ≠ Sum.elim (Finsupp.weight (blockWeight ι) d) 0 :=
        fun e => hb (funext fun k => congrFun e (Sum.inl k))
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj hb', map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (liftVar (ι := ι) ι'))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inl k)
    exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinPointVerticalDivisor


open JoinPointVerticalDivisor in
theorem JoinPointVerticalDivisor.proof : JoinPointVerticalDivisor.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ y b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨Sum.elim α 0, Sum.elim β 0, isMultiHomog_rename hf, isMultiHomog_rename hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k)
    · simpa [pullDeg] using hb k
    · simp [pullDeg]
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O y ≤ Q.comap (rename (liftVar (ι := ι) ptIdx)) := fun h hh =>
      Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O y ptCoord h).mpr hh))
    have hO : (Q.comap (rename (liftVar (ι := ι) ptIdx))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (liftVar ptIdx) u, rename (liftVar ptIdx) v, ⟨_, isMultiHomog_rename hu⟩,
      ⟨_, isMultiHomog_rename hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O y ptCoord _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

