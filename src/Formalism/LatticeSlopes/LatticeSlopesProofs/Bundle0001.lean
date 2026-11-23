module

public import Formalism.LatticeSlopes.Statement

@[expose] public section

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
section
open Module Submodule

noncomputable section

namespace Formalism.F

theorem gram_sum_smul_eq_transpose_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] (v : ι → E) (P : Matrix ι κ ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, P i j • v i) = P.transpose * Matrix.gram ℝ v * P := by
  ext j k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem det_gram_basis_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℤ L) (c : Basis κ ℤ L) :
    (Matrix.gram ℝ (fun i => (b i : E))).det = (Matrix.gram ℝ (fun k => (c k : E))).det := by
  let e : ι ≃ κ := b.indexEquiv c
  let c' : Basis ι ℤ L := c.reindex e.symm
  have hc' : (Matrix.gram ℝ (fun k => (c k : E))).det = (Matrix.gram ℝ (fun i => (c' i : E))).det := by
    have hs : Matrix.gram ℝ (fun i => (c' i : E)) = (Matrix.gram ℝ (fun k => (c k : E))).submatrix e e := by
      ext i j
      simp [c', Matrix.gram_apply]
    rw [hs, Matrix.det_submatrix_equiv_self]
  rw [hc']
  let M : Matrix ι ι ℤ := c'.toMatrix b
  have hb : (fun i => (b i : E)) = fun i => ∑ k, (M.map (Int.cast : ℤ → ℝ)) k i • (c' k : E) := by
    funext i
    conv_lhs => rw [← c'.sum_repr (b i)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Matrix.map_apply, Int.cast_smul_eq_zsmul]
    rfl
  rw [hb, gram_sum_smul_eq_transpose_mul (fun k => (c' k : E)) (M.map (Int.cast : ℤ → ℝ)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet : (M.map (Int.cast : ℤ → ℝ)).det ^ 2 = 1 := by
    have h2 : M.det * (b.toMatrix c').det = 1 := by
      rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip c' b, Matrix.det_one]
    have h3 : IsUnit M.det :=
      ⟨⟨M.det, (b.toMatrix c').det, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    rw [← Int.cast_det]
    rcases Int.isUnit_iff.1 h3 with h | h <;> rw [h] <;> norm_num
  linear_combination (Matrix.gram ℝ (fun i => (c' i : E))).det * hdet

theorem covol_eq_gram : CovolEqGram := by
  intro E _ _ _ L hL ι _ _ b
  unfold covol
  rw [dite_eq_left hL]
  congr 1
  exact det_gram_basis_eq L (Module.finBasis ℤ L) b

end Formalism.F
end
end

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
section
namespace Formalism.F

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_of_le {L N : Submodule ℤ E} (h : N ≤ L) [hL : DiscreteTopology L] :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (f := Submodule.inclusion h)
    (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective h)

end Formalism.F
end

-- bundled from Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
section
open Module

noncomputable section

namespace Formalism.F

theorem normDet_le_pow_finrank {R F : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : R →ₗ[ℝ] F) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ y, ‖g y‖ ≤ K * ‖y‖) :
    g.normDet ≤ K ^ finrank ℝ R := by
  by_cases h : Nonempty (OrthonormalBasis (Fin (finrank ℝ R)) ℝ g.range)
  swap
  · have hg0 : g.normDet = 0 := (g.normDet_eq_zero_tfae.out 5 1).mp (not_nonempty_iff.mp h)
    rw [hg0]
    positivity
  rw [g.normDet_eq_norm_det_toMatrix_rangeRestrict (stdOrthonormalBasis ℝ R) h.some]
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩

  let φ : LinearMap.range g ≃ₗᵢ[ℝ] R := h.some.repr.trans (stdOrthonormalBasis ℝ R).repr.symm
  let T : R →ₗ[ℝ] R := φ.toLinearEquiv.toLinearMap ∘ₗ g.rangeRestrict
  have hmat : LinearMap.toMatrix (stdOrthonormalBasis ℝ R).toBasis h.some.toBasis g.rangeRestrict =
      LinearMap.toMatrix (stdOrthonormalBasis ℝ R).toBasis (stdOrthonormalBasis ℝ R).toBasis T := by
    ext i j
    simp [LinearMap.toMatrix_apply, T, φ]
  rw [hmat, LinearMap.det_toMatrix, Real.norm_eq_abs]
  have hT : ∀ y, ‖T y‖ = ‖g y‖ := by
    intro y
    simp [T]
  have hsub : T '' Metric.ball 0 1 ⊆ Metric.closedBall 0 K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff] at hy
    rw [mem_closedBall_zero_iff, hT]
    calc ‖g y‖ ≤ K * ‖y‖ := hg y
      _ ≤ K * 1 := by gcongr
      _ = K := mul_one K
  have hm := MeasureTheory.measure_mono (μ := (MeasureTheory.volume : MeasureTheory.Measure R)) hsub
  rw [MeasureTheory.Measure.addHaar_image_linearMap, MeasureTheory.Measure.addHaar_closedBall _ _ hK] at hm
  have hpos : 0 < MeasureTheory.volume (Metric.ball (0 : R) 1) := Metric.measure_ball_pos _ _ one_pos
  have hfin : MeasureTheory.volume (Metric.ball (0 : R) 1) ≠ ⊤ := MeasureTheory.measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin).1 hm
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

def linearCombinationMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

theorem linearCombinationMap_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) (c : EuclideanSpace ℝ ι) :
    linearCombinationMap v c = ∑ i, c i • v i := rfl

private theorem det_gram_eq_zero_of_linearCombination_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (c : EuclideanSpace ℝ ι) (hc : c ≠ 0)
    (h0 : linearCombinationMap v c = 0) : (Matrix.gram ℝ v).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => c i, ?_, ?_⟩
  · intro h
    apply hc
    ext i
    exact congrFun h i
  · ext i
    rw [linearCombinationMap_apply] at h0
    have h1 : inner ℝ (v i) (∑ j, c j • v j) = 0 := by rw [h0, inner_zero_right]
    rw [inner_sum] at h1
    simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, real_inner_smul_right, mul_comm] using h1

private theorem gram_linearCombinationMap_eq_toMatrix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (v : ι → E)
    (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ ι)) :
    Matrix.gram ℝ (fun k => linearCombinationMap v (b k)) =
      LinearMap.toMatrix b.toBasis b.toBasis
        (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ (linearCombinationMap v).rangeRestrict) := by
  ext k l
  rw [Matrix.gram_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, OrthonormalBasis.repr_apply_apply,
    LinearMap.adjoint_inner_right]
  rfl

theorem det_gram_eq_normDet_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) :
    (Matrix.gram ℝ v).det = (linearCombinationMap v).normDet ^ 2 := by
  have hv : v = fun i => linearCombinationMap v (EuclideanSpace.basisFun ι ℝ i) := by
    funext i
    rw [linearCombinationMap_apply]
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_smul]
  have h1 : (Matrix.gram ℝ v).det = LinearMap.det (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ
      (linearCombinationMap v).rangeRestrict) := by
    conv_lhs => rw [hv]
    rw [gram_linearCombinationMap_eq_toMatrix, LinearMap.det_toMatrix]
  by_cases h : Nonempty (OrthonormalBasis (Fin (finrank ℝ (EuclideanSpace ℝ ι))) ℝ
    (linearCombinationMap v).range)
  · rw [(linearCombinationMap v).normDet_eq_norm_det_toMatrix_rangeRestrict
      (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)) h.some]
    have h2 : (Matrix.gram ℝ (fun k => linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))).det =
        LinearMap.det (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ
          (linearCombinationMap v).rangeRestrict) := by
      rw [gram_linearCombinationMap_eq_toMatrix, LinearMap.det_toMatrix]
    rw [h1, ← h2]
    have hG : Matrix.gram ℝ (fun k => linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k)) =
        (LinearMap.toMatrix (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)).toBasis h.some.toBasis
          (linearCombinationMap v).rangeRestrict).transpose *
        LinearMap.toMatrix (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)).toBasis h.some.toBasis
          (linearCombinationMap v).rangeRestrict := by
      ext k l
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis]
      have e1 : inner ℝ (linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))
          (linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) l)) =
          inner ℝ ((linearCombinationMap v).rangeRestrict (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))
            ((linearCombinationMap v).rangeRestrict (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) l)) := rfl
      rw [e1, ← h.some.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [real_inner_comm (h.some m) ((linearCombinationMap v).rangeRestrict _),
        ← OrthonormalBasis.repr_apply_apply, ← OrthonormalBasis.repr_apply_apply]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, Real.norm_eq_abs, sq_abs, sq]
  · have hni : ¬ Function.Injective (linearCombinationMap v) := by
      intro hinj
      exact h ⟨(stdOrthonormalBasis ℝ (LinearMap.range (linearCombinationMap v))).reindex
        (finCongr (LinearMap.finrank_range_of_inj hinj))⟩
    rw [← LinearMap.ker_eq_bot] at hni
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hni, zero_pow two_ne_zero]
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hni
    exact det_gram_eq_zero_of_linearCombination_eq_zero v c hc0 (LinearMap.mem_ker.1 hc)

theorem gram_det_le : GramDetLe := by
  intro E F _ _ _ _ ι _ _ v w C hC
  have hvw : ∀ c : EuclideanSpace ℝ ι,
      ‖linearCombinationMap w c‖ ≤ C * ‖linearCombinationMap v c‖ := by
    intro c
    simpa only [linearCombinationMap_apply] using hC (fun i => c i)
  by_cases hinj : Function.Injective (linearCombinationMap v)
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Matrix.det_isEmpty]
    have hC0 : 0 ≤ C := by
      by_contra hneg
      push_neg at hneg
      obtain ⟨i⟩ := hι
      have h1 := hvw (EuclideanSpace.single i 1)
      have h3 : ‖linearCombinationMap v (EuclideanSpace.single i 1)‖ ≤ 0 := by
        nlinarith [norm_nonneg (linearCombinationMap v (EuclideanSpace.single i 1)),
          norm_nonneg (linearCombinationMap w (EuclideanSpace.single i 1))]
      have h4 := hinj ((norm_le_zero_iff.1 h3).trans (map_zero _).symm)
      have h5 := congrArg (fun x : EuclideanSpace ℝ ι => x i) h4
      simp at h5
    let e := LinearEquiv.ofInjective (linearCombinationMap v) hinj
    let G : E →ₗ[ℝ] F := linearCombinationMap w ∘ₗ e.symm.toLinearMap ∘ₗ
      ((LinearMap.range (linearCombinationMap v)).orthogonalProjection :
        E →ₗ[ℝ] LinearMap.range (linearCombinationMap v))
    have hP : ∀ y : LinearMap.range (linearCombinationMap v),
        (LinearMap.range (linearCombinationMap v)).orthogonalProjection (y : E) = y := fun y =>
      Submodule.orthogonalProjection_mem_subspace_eq_self y
    have hGf : G ∘ₗ linearCombinationMap v = linearCombinationMap w := by
      ext c
      have : linearCombinationMap v c = (e c : E) := (LinearEquiv.ofInjective_apply _ c).symm
      simp only [G, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_toLinearMap]
      rw [this, hP, LinearEquiv.symm_apply_apply]
    have hb : ∀ y : LinearMap.range (linearCombinationMap v),
        ‖G.domRestrict (LinearMap.range (linearCombinationMap v)) y‖ ≤ C * ‖y‖ := by
      intro y
      have hy : linearCombinationMap v (e.symm y) = (y : E) := by
        rw [← LinearEquiv.ofInjective_apply (h := hinj) (linearCombinationMap v) (e.symm y)]
        exact congrArg Subtype.val (e.apply_symm_apply y)
      simp only [LinearMap.domRestrict_apply, G, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        LinearEquiv.coe_toLinearMap]
      rw [hP]
      calc ‖linearCombinationMap w (e.symm y)‖ ≤ C * ‖linearCombinationMap v (e.symm y)‖ := hvw _
        _ = C * ‖y‖ := by rw [hy]; rfl
    have hdom := normDet_le_pow_finrank (G.domRestrict (LinearMap.range (linearCombinationMap v))) C hC0 hb
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace] at hdom
    have hle : (linearCombinationMap w).normDet ≤
        C ^ Fintype.card ι * (linearCombinationMap v).normDet := by
      rw [← hGf, LinearMap.normDet_comp]
      exact mul_le_mul_of_nonneg_right hdom (LinearMap.normDet_nonneg _)
    rw [det_gram_eq_normDet_sq w, det_gram_eq_normDet_sq v]
    calc (linearCombinationMap w).normDet ^ 2
        ≤ (C ^ Fintype.card ι * (linearCombinationMap v).normDet) ^ 2 :=
          pow_le_pow_left₀ (LinearMap.normDet_nonneg _) hle 2
      _ = C ^ (2 * Fintype.card ι) * (linearCombinationMap v).normDet ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2]
  · rw [← LinearMap.ker_eq_bot] at hinj
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hinj
    have hw0 : linearCombinationMap w c = 0 := by
      have h1 := hvw c
      rw [LinearMap.mem_ker.1 hc, norm_zero, mul_zero] at h1
      exact norm_le_zero_iff.1 h1
    rw [det_gram_eq_zero_of_linearCombination_eq_zero w c hc0 hw0]
    exact mul_nonneg (by rw [pow_mul]; positivity) (Matrix.posSemidef_gram ℝ v).det_nonneg

end Formalism.F
end
end

