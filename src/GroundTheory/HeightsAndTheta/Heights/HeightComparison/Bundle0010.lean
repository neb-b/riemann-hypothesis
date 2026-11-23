module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


omit [Fintype ι] [DecidableEq ι] in
theorem val_chartEval_eq_aeval_div (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : chartRing x c) : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), Subalgebra.coe_add, IntermediateField.coe_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp]
    simp [chartEval, chartRatio]


omit [Fintype ι] [DecidableEq ι] in
theorem chartEval_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by
  rintro ⟨a, ha⟩
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  refine ⟨f, Subtype.ext ?_⟩
  have h : (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) :=
    MvPolynomial.algHom_ext fun p ↦ by simp [chartEval]
  exact AlgHom.congr_fun h f


omit [Fintype ι] [DecidableEq ι] in
theorem mem_ker_chartEval_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ RingHom.ker (chartEval x c) ↔ aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0 := by
  rw [RingHom.mem_ker, ← val_chartEval_eq_aeval_div]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)

theorem aeval_blockScale_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (t : ι → Ω) (w : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    aeval (fun p ↦ t p.1 * w p) g = (∏ k, t k ^ m k) * aeval w g := by
  have h : algebraMap ℤ Ω = Int.castRingHom Ω := Subsingleton.elim _ _
  rw [aeval_def, aeval_def, h]
  exact eval₂_scale_of_isWeightedHomogeneous t w hg

theorem ker_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    RingHom.ker (chartEval x c) = orbitIdeal x ⊔
      Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
  set J := Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) with hJ
  set z : Coord n → AlgebraicClosure ℚ := fun p ↦ x p.1 p.2 / x p.1 (c p.1) with hz
  apply le_antisymm
  · intro f hf
    rw [mem_ker_chartEval_iff] at hf
    set N : ι → ℕ := fun k ↦ (compDegs f).sup fun m ↦ m k with hN
    have hle : ∀ m ∈ compDegs f, m ≤ N := fun m hm k ↦ Finset.le_sup (f := fun m : ι → ℕ ↦ m k) hm
    set F := ∑ m ∈ compDegs f,
      weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m) with hF
    have hFJ : f - F ∈ J := by
      have h1 : ∀ d, Ideal.Quotient.mk J (chartMonomial c d) = 1 := by
        intro d
        rw [chartMonomial, map_prod]
        refine Finset.prod_eq_one fun k _ ↦ ?_
        have hk : Ideal.Quotient.mk J (X ⟨k, c k⟩) = 1 := by
          rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
          exact Ideal.subset_span ⟨k, rfl⟩
        rw [map_pow, hk, one_pow]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq, hF, map_sum]
      simp only [map_mul, h1, mul_one]
      conv_lhs => rw [← sum_compDegs f]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
    have hFP : F ∈ orbitIdeal x := by
      have hhom : IsWeightedHomogeneous (coordDeg n) F N := by
        have : F ∈ weightedHomogeneousSubmodule ℤ (coordDeg n) N := by
          refine Submodule.sum_mem _ fun m hm ↦ ?_
          have h2 := (weightedHomogeneousComponent_isWeightedHomogeneous m f).mul
            (isWeightedHomogeneous_chartMonomial c (N - m))
          rwa [add_tsub_cancel_of_le (hle m hm)] at h2
        exact this
      rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hhom]
      have hy : flatCone x = fun p ↦ x p.1 (c p.1) * z p := by
        funext p
        simp only [hz, flatCone]
        rw [mul_div_cancel₀ _ (hc p.1)]
      have hterm : ∀ m ∈ compDegs f,
          aeval (flatCone x) (weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m)) =
            (∏ k, x k (c k) ^ N k) * aeval z (weightedHomogeneousComponent (coordDeg n) m f) := by
        intro m hm
        have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ x k (c k)) z
          (weightedHomogeneousComponent_isWeightedHomogeneous m f)
        have hmon : aeval (flatCone x) (chartMonomial c (N - m)) = ∏ k, x k (c k) ^ (N k - m k) := by
          simp [chartMonomial, map_prod, flatCone]
        have hpow : ∏ k, x k (c k) ^ N k = (∏ k, x k (c k) ^ m k) * ∏ k, x k (c k) ^ (N k - m k) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [← pow_add, Nat.add_sub_cancel' (hle m hm k)]
        rw [map_mul, hmon, hpow]
        rw [hy]
        rw [hs]
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, map_sum]
      refine (Finset.sum_congr rfl hterm).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Finset.mul_sum, ← map_sum, sum_compDegs, show aeval z f = 0 from hf, mul_zero]
    have : f = F + (f - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hFJ)
  · refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    · rw [mem_ker_chartEval_iff]
      rw [orbitIdeal, mem_mCoordIdeal_iff] at hf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_compDegs f, map_sum]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ (x k (c k))⁻¹) (flatCone x)
        (weightedHomogeneousComponent_isWeightedHomogeneous m f)
      have hz' : (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) =
          fun p ↦ (x p.1 (c p.1))⁻¹ * flatCone x p := by
        funext p
        rw [div_eq_inv_mul]
        rfl
      rw [hz', hs]
      refine mul_eq_zero_of_right _ ?_
      have h0 := hf m
      rw [aeval_def, Subsingleton.elim (algebraMap ℤ _) (Int.castRingHom _)] at h0 ⊢
      exact h0
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, mem_ker_chartEval_iff]
      simp [div_self (hc k)]

theorem OrbitChartQuot.proof : OrbitChartQuot.Statement := by
  intro ι _ _ n x c hc V hV
  have hsurj := chartEval_surjective x c
  let g : MvPolynomial (Coord n) ℤ →+* chartRing x c ⧸ chartPoint x c V :=
    (Ideal.Quotient.mk _).comp (chartEval x c : MvPolynomial (Coord n) ℤ →+* chartRing x c)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hsurj
  have hker : RingHom.ker g =
      V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
    ext f
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (chartEval x c f) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, chartPoint,
      Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, ker_chartEval x c hc,
      ← sup_assoc, sup_eq_left.mpr hV]
  exact ⟨(RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hker)⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval₂_mul_block_of_isMultiHomog {R : Type*} [CommRing R] (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (g : ℤ →+* R) (y : Coord n → R)
    (t : ι → R) :
    eval₂ g (fun p ↦ y p * t p.1) s = eval₂ g y s * ∏ k, t k ^ a k := by
  classical
  simp only [eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  change ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
  rw [Finset.prod_pow_eq_pow_sum, hs m hm k]


omit [Fintype ι] in
theorem coe_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  have h : (((ratioField x).val.restrictScalars ℤ).comp (chartRing x c).val).comp (chartEval x c) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) :=
    algHom_ext fun p ↦ by simp [chartEval, chartRatio]
  exact DFunLike.congr_fun h f

theorem evalCone_ne_zero_of_notMem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hW : s ∉ orbitIdeal x) : evalCone x s ≠ 0 := by
  intro h0
  apply hW
  have hC : ∀ g : ℤ →+* MvPolynomial ι (AlgebraicClosure ℚ),
      eval₂ g (fun p ↦ C (flatCone x p)) s = C (evalCone x s) := fun g ↦ by
    rw [evalCone, eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_def,
    eval₂_mul_block_of_isMultiHomog s a hs _ (fun p ↦ C (flatCone x p)) X, hC, h0, map_zero,
    zero_mul]


omit [Fintype ι] in
theorem coe_evalCone_coordVec (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ) :
    ((evalCone (coordVec x) s : coordField x) : AlgebraicClosure ℚ) = evalCone x s := by
  have h := eval₂_comp_left (algebraMap (coordField x) (AlgebraicClosure ℚ)) (Int.castRingHom _)
    (fun v ↦ coordVec x v.1 v.2) s
  rw [RingHom.ext_int ((algebraMap (coordField x) (AlgebraicClosure ℚ)).comp (Int.castRingHom _))
    (Int.castRingHom _)] at h
  exact h

theorem OrbitChartTerm.proof : OrbitChartTerm.Statement := by
  intro ι _ _ n A x s hs c hxc
  obtain ⟨a, ha, hhom, hW⟩ := hs
  have hfac : evalCone x s =
      ((chartEval x c s : ratioField x) : AlgebraicClosure ℚ) * ∏ k, x k (c k) ^ a k := by
    rw [coe_chartEval, aeval_def, ← eval₂_mul_block_of_isMultiHomog s a hhom _
      (fun p ↦ x p.1 p.2 / x p.1 (c p.1)) (fun k ↦ x k (c k)), evalCone]
    congr 1
    funext p
    exact (div_mul_cancel₀ _ (hxc p.1)).symm
  have hx0 : evalCone x s ≠ 0 := evalCone_ne_zero_of_notMem_orbitIdeal x s a hhom hW
  have hf0 : chartEval x c s ≠ 0 := by
    intro h
    rw [h] at hfac
    simp at hfac
    exact hx0 hfac
  refine ⟨hf0, fun v hv ↦ ?_⟩
  have hsup : ∀ k, ⨆ i, v (coordVec x k i) = v (coordVec x k (c k)) := fun k ↦
    le_antisymm (not_lt.mp fun h ↦ hv k (X_mem_orbitCenter x v k (c k) h))
      (le_ciSup (f := fun i ↦ v (coordVec x k i)) (Finite.bddAbove_range _) (c k))
  have hK : evalCone (coordVec x) s =
      IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s) *
        ∏ k, coordVec x k (c k) ^ a k := by
    apply Subtype.ext
    rw [coe_evalCone_coordVec, hfac, MulMemClass.coe_mul, IntermediateField.coe_prod,
      IntermediateField.coe_inclusion]
    simp only [SubmonoidClass.coe_pow]
    rfl
  have hc0 : ∀ k, 0 < v (coordVec x k (c k)) := fun k ↦
    FinitePlace.pos_iff.mpr fun h ↦ hxc k (congrArg Subtype.val h)
  have hv0 : 0 < v (IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s)) :=
    FinitePlace.pos_iff.mpr fun h ↦ hf0 (Subtype.ext
      ((IntermediateField.inclusion (ratioField_le_coordField x)).injective
        (h.trans (map_zero _).symm)))
  have ha' : ∀ k, (A.deg k : ℝ) = (a k : ℝ) := fun k ↦ by
    have h := ha k
    rw [HermLine.toGeo_a] at h
    exact_mod_cast h
  rw [hK, map_mul, map_prod, Real.log_mul hv0.ne' (Finset.prod_pos fun k _ ↦ (by
      rw [map_pow]; exact pow_pos (hc0 k) _)).ne',
    Real.log_prod fun k _ ↦ (by rw [map_pow]; exact (pow_pos (hc0 k) _).ne'), finiteTerm]
  simp only [map_pow, Real.log_pow, hsup, ha']
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitLocalSum.proof (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement) :
    OrbitLocalSum.Statement := by
  intro ι _ _ _ n A x s hx hs V hV
  obtain ⟨hVmin, hVrel⟩ := id hV
  choose c hc using hVrel
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hxc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hc k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  obtain ⟨hft, hfr⟩ := hR ι n x c hxc
  have := hM ι n A x s hx hs V hV c hc
  obtain ⟨hf0, hterm⟩ := hT ι n A x s hs c hxc
  let _ : Algebra (ratioField x) (coordField x) :=
    (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.toAlgebra
  have hset : {v : FinitePlace (coordField x) | orbitCenter x v = V} =
      {v : FinitePlace (coordField x) | AbsCentredAt (chartRing x c) (chartPoint x c V)
        fun u ↦ v (algebraMap (ratioField x) (coordField x) u)} :=
    Set.ext fun v ↦ hC ι n A x s hx hs V hV c hc v
  have hsum : ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
        -Real.log (v (algebraMap (ratioField x) (coordField x) (chartEval x c s))) :=
    finsum_mem_congr rfl fun v hv ↦ hterm v fun k hk ↦ hc k (by
      rw [← (show orbitCenter x v = V from hv)]
      exact hk)
  have hdeg := (letI : Module.Free (ratioField x) (coordField x) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (ratioField x) (coordField x))
  rw [hsum, hset, hS (ratioField x) (coordField x) (chartRing x c) (chartPoint x c V),
    hU ι n A x s hx hs V hV c hc, hF ι n A x s hx hs V hV c hc,
    ← hP (ratioField x) (chartRing x c) hft hfr (chartPoint x c V) (chartEval x c s) hf0, ← hdeg]
  push_cast
  ring_nf
  rfl

end GroundTheory.Heights₂.Heights
end

