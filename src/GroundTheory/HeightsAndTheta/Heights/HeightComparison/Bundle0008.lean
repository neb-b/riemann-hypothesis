module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitCenterPrime.proof (hIff : OrbitCenterMemIff.Statement) :
    OrbitCenterPrime.Statement := by
  intro ι _ _ n x hx v
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let w : Coord n → Lex (ι → ℕ) := fun c ↦ toLex (coordDeg n c)
  let _ : DecidableEq (Lex (ι → ℕ)) := LinearOrder.toDecidableEq
  have _ : GradedRing (weightedHomogeneousSubmodule ℤ w) := MvPolynomial.weightedGradedAlgebra ℤ w
  have hw : ∀ (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
      IsWeightedHomogeneous w F (toLex d) ↔ IsWeightedHomogeneous (coordDeg n) F d :=
    fun _ _ ↦ Iff.rfl
  set M : (ι → ℕ) → ℝ := fun d ↦ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k with hM
  have hM0 : ∀ d, 0 ≤ M d := fun d ↦
    Finset.prod_nonneg fun k _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg v _) _
  have hMadd : ∀ d e, M (d + e) = M d * M e := fun d e ↦ by
    simp only [hM, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hform : ∀ F, SetLike.IsHomogeneousElem (weightedHomogeneousSubmodule ℤ w) F →
      ∃ d, Geo.IsMultiHomog (ι := blockIdx n) F d := by
    rintro F ⟨i, hi⟩
    exact ⟨ofLex i, (geoMultiHomog_iff _ _).mpr
      ((hw F (ofLex i)).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hi))⟩
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := weightedHomogeneousSubmodule ℤ w) ?_ ?_ ?_
  · refine Ideal.homogeneous_span _ _ ?_
    rintro F ⟨d, hd, -⟩
    exact ⟨toLex d, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      ((hw F d).mpr ((geoMultiHomog_iff _ _).mp hd))⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    intro h
    have h1 : Geo.IsMultiHomog (ι := blockIdx n) (1 : MvPolynomial (Coord n) ℤ) 0 :=
      (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_one ℤ _)
    have := (hIff ι n x hx v 1 0 h1).mp h
    simp [evalCone] at this
  · intro F G hF hG hFG
    obtain ⟨d, hd⟩ := hform F hF
    obtain ⟨e, he⟩ := hform G hG
    have hde : Geo.IsMultiHomog (ι := blockIdx n) (F * G) (d + e) :=
      (geoMultiHomog_iff _ _).mpr
        (((geoMultiHomog_iff _ _).mp hd).mul ((geoMultiHomog_iff _ _).mp he))
    have hlt := (hIff ι n x hx v _ _ hde).mp hFG
    by_contra! hno
    have h1 := not_lt.mp (mt (hIff ι n x hx v F d hd).mpr hno.1)
    have h2 := not_lt.mp (mt (hIff ι n x hx v G e he).mpr hno.2)
    rw [evalCone, eval₂_mul, map_mul, ← evalCone, ← evalCone] at hlt
    have := mul_le_mul h1 h2 (hM0 e) (apply_nonneg v _)
    rw [← hMadd] at this
    exact absurd hlt (not_lt.mpr this)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDivVertical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem exists_int_poly_coeff_zero_ne_zero {τ : AlgebraicClosure ℚ} (hτ : τ ≠ 0) :
    ∃ P : Polynomial ℤ, P.coeff 0 ≠ 0 ∧ Polynomial.aeval τ P = 0 := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  obtain ⟨Q, hQ, hQτ⟩ :=
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic τ⁻¹).restrictScalars (R := ℤ)
  have : Invertible τ⁻¹ := invertibleOfNonzero (inv_ne_zero hτ)
  refine ⟨Q.reverse, by rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ, ?_⟩
  have h := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℤ (AlgebraicClosure ℚ)) τ⁻¹ Q).mpr hQτ
  rwa [invOf_eq_inv, inv_inv] at h

theorem OrbitDivVertical.proof : OrbitDivVertical.Statement := by
  intro ι _ _ _ n A x s _ hs V hV hH
  obtain ⟨a, -, hsa, hsW⟩ := hs
  obtain ⟨hVmin, hVrel⟩ := hV
  have hVp : V.IsPrime := hVmin.1.1
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hsV : s ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  choose c hc using hVrel
  set M : MvPolynomial (Coord n) ℤ := chartMonomial c a with hMdef
  have hMV : M ∉ V := by
    rw [hMdef, chartMonomial]
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hVp)).mp h
    exact hc k (hVp.mem_of_pow_mem _ hk)
  have hMa : Geo.IsMultiHomog (ι := blockIdx n) M a :=
    (geoMultiHomog_iff _ a).mpr (isWeightedHomogeneous_chartMonomial c a)
  set y := flatCone x
  set T : MvPolynomial ι (AlgebraicClosure ℚ) := ∏ k, X k ^ a k
  set σ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y s
  set μ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y M
  have hφs : Geo.mConeMap (ι := blockIdx n) y s = C σ * T := mConeMap_of_isMultiHomog y s a hsa
  have hφM : Geo.mConeMap (ι := blockIdx n) y M = C μ * T := mConeMap_of_isMultiHomog y M a hMa
  have hσ : σ ≠ 0 := fun h ↦ hsW (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφs, h, map_zero, zero_mul])
  have hμ : μ ≠ 0 := fun h ↦ hMV (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφM, h, map_zero, zero_mul]))
  obtain ⟨P, hP0, hP⟩ := exists_int_poly_coeff_zero_ne_zero (div_ne_zero hσ hμ)
  set m := P.natDegree
  let f : ℕ → MvPolynomial (Coord n) ℤ := fun j ↦ C (P.coeff j) * s ^ j * M ^ (m - j)
  have hfW : ∑ j ∈ Finset.range (m + 1), f j ∈ orbitIdeal x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, map_sum]
    have hterm : ∀ j ∈ Finset.range (m + 1), Geo.mConeMap (ι := blockIdx n) y (f j) =
        C (algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) * (σ / μ) ^ j * μ ^ m) * T ^ m := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have e1 : (σ / μ) ^ j * μ ^ m = σ ^ j * μ ^ (m - j) := by
        rw [← Nat.add_sub_cancel' hjm, pow_add, Nat.add_sub_cancel_left, div_pow, ← mul_assoc,
          div_mul_cancel₀ _ (pow_ne_zero _ hμ)]
      have e2 : T ^ m = T ^ j * T ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' hjm]
      simp only [f, map_mul, map_pow, hφs, hφM, MvPolynomial.algHom_C, mul_assoc, e1, e2]
      simp only [eq_intCast, map_intCast, mul_pow]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, ← Finset.sum_mul]
    have hPτ : ∑ j ∈ Finset.range (m + 1), algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) *
        (σ / μ) ^ j = 0 := by
      rw [← hP, Polynomial.aeval_eq_sum_range]
      simp [Algebra.smul_def]
      rfl
    rw [hPτ, zero_mul, map_zero, zero_mul]
  have hrest : ∑ j ∈ Finset.range m, f (j + 1) ∈ V :=
    Ideal.sum_mem _ fun j _ ↦ by
      simp only [f]
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hsV))
  have h0 : f 0 ∈ V := by
    have h := Ideal.sub_mem V (hWV hfW) hrest
    rwa [Finset.sum_range_succ', add_sub_cancel_left] at h
  simp only [f, pow_zero, mul_one, Nat.sub_zero] at h0
  rcases hVp.mem_or_mem h0 with hC | hM
  · apply hP0
    have : P.coeff 0 ∈ V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hC
    rw [show V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from hH] at this
    exact (Ideal.mem_bot).mp this
  · exact hMV (hVp.mem_of_pow_mem _ hM)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitFiniteSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

theorem OrbitFiniteSum.proof (hD : OrbitDegreeRatio.Statement) (hL : OrbitLocalSum.Statement)
    (hZ : OrbitCenterZero.Statement) : OrbitFiniteSum.Statement := by
  classical
  intro ι _ _ _ n A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hS := ((finite_support_height A x hx).union hsupp2).subset
    (Function.support_sub (fun v : FinitePlace (coordField x) ↦ finiteTerm A v (coordVec x)) _)
  have hsubF : Function.support (fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) ⊆ hS.toFinset := by
    simp
  have hK : (0 : ℝ) < Module.finrank ℚ (coordField x) := by exact_mod_cast Module.finrank_pos
  have hloc : ∀ V, ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ v ∈ hS.toFinset, if orbitCenter x v = V then
        finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0 := by
    intro V
    rw [finsum_mem_def, finsum_eq_sum_of_support_subset _
      (by rw [Set.support_indicator]; exact Set.inter_subset_right.trans hsubF)]
    exact Finset.sum_congr rfl fun v _ ↦ by simp [Set.indicator_apply]
  have hterm : ∀ V ∈ (Geo.divSupp_finite (orbitIdeal x) s).toFinset,
      (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V)) =
        (∑ v ∈ hS.toFinset, if orbitCenter x v = V then
          finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0) *
          (Module.finrank ℚ (ratioField x) / Module.finrank ℚ (coordField x) : ℝ) := fun V hV ↦ by
    have h := hL ι n A x s hx hs V ((Geo.divSupp_finite _ _).mem_toFinset.mp hV)
    rw [hloc V] at h
    rw [mul_div_assoc', eq_div_iff hK.ne', mul_comm _ (Module.finrank ℚ (ratioField x) : ℝ), ← h,
      mul_comm]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Geo.divSupp_finite _ _), Finset.sum_congr rfl hterm,
    ← Finset.sum_mul, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun v _ ↦ by
      split_ifs with h
      · rfl
      · exact (hZ ι n A x s hx hs v fun h' ↦ h ((Geo.divSupp_finite _ _).mem_toFinset.mpr h')).symm,
    ← finsum_eq_sum_of_support_subset _ hsubF, hD ι n x hx]
  ring

end GroundTheory.Heights₂.Heights
end

