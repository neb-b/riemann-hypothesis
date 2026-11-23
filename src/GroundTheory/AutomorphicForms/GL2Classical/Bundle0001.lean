module

public import Mathlib
public import GroundTheory.AutomorphicForms.GL2Classical.ConstantTerm
public import GroundTheory.AutomorphicForms.GL2Classical.Growth
public import GroundTheory.GlobalFields.TateThesis.Bundle0009
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Bundle0001

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.GL2Classical.CuspConverse
section
open NumberField IsDedekindDomain Matrix MeasureTheory Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global ModularForm

theorem continuous_vadd_upperHalfPlane (z : ℍ) : Continuous fun t : ℝ => t +ᵥ z := by
  refine UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 ?_
  have : ((↑) ∘ fun t : ℝ => t +ᵥ z) = fun t : ℝ => (t : ℂ) + (z : ℂ) := by
    funext t
    simp only [Function.comp_apply, coe_vadd]
  rw [this]
  fun_prop

theorem periodic_comp_ofComplex_of_vadd {F : ℍ → ℂ} {M : ℝ} (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) :
    Function.Periodic (F ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push Not at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem tendsto_atImInfty_of_periodic_of_mdifferentiable {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F) :
    Tendsto F atImInfty (𝓝 (cuspFunction M F 0)) := by
  have hfper := periodic_comp_ofComplex_of_vadd hper
  have han := analyticAt_cuspFunction_zero hM hfper hhol hbdd
  have e : (cuspFunction M F ∘ fun τ : ℍ => Function.Periodic.qParam M τ) = F := by
    funext τ
    simpa using eq_cuspFunction τ hM.ne' hfper
  simpa [e] using han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hM)

theorem isZeroAtImInfty_of_integral_vadd_eq_zero {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F)
    (hint : ∀ z : ℍ, ∫ t in (0 : ℝ)..M, F (t +ᵥ z) = 0) : IsZeroAtImInfty F := by
  set c := cuspFunction M F 0
  have ht := tendsto_atImInfty_of_periodic_of_mdifferentiable hM hper hhol hbdd
  suffices hc : c = 0 by
    rw [IsZeroAtImInfty, ZeroAtFilter, ← hc]
    exact ht
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (ht.eventually (Metric.closedBall_mem_nhds c hε))
  have hY : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set z₀ : ℍ := ⟨(max A 1 : ℝ) * Complex.I, by simp [hY]⟩
  have hbound : ∀ t : ℝ, ‖F (t +ᵥ z₀) - c‖ ≤ ε := by
    intro t
    have hz : A ≤ (t +ᵥ z₀).im := by
      rw [vadd_im]
      show A ≤ ((max A 1 : ℝ) * Complex.I).im
      simp
    have := hA _ hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hcont : Continuous fun t : ℝ => F (t +ᵥ z₀) :=
    hhol.continuous.comp (continuous_vadd_upperHalfPlane z₀)
  have hint' : ∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c) = -(M • c) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const, hint z₀,
      intervalIntegral.integral_const, sub_zero, zero_sub]
  have hle : ‖∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c)‖ ≤ ε * |M - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hbound t
  rw [hint', norm_neg, norm_smul, Real.norm_eq_abs, sub_zero, abs_of_pos hM] at hle
  exact le_of_mul_le_mul_left (by linarith [hle] : M * ‖c‖ ≤ M * ε) hM

variable {N : ℕ} [NeZero N] {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.GL2Classical.KFinite
section
open NumberField IsDedekindDomain Matrix Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem realPart_orthogonal {x : AdelicGL ℚ 2} (hx : x ∈ Reduction.maxCompact) :
    realPart x 0 0 ^ 2 + realPart x 0 1 ^ 2 = 1 ∧ realPart x 1 0 ^ 2 + realPart x 1 1 ^ 2 = 1 ∧
      realPart x 0 0 * realPart x 1 0 + realPart x 0 1 * realPart x 1 1 = 0 := by
  set w0 : InfinitePlace ℚ := default
  have hw0 := RationalIdeles.isReal_infinitePlace w0
  have hn := (Reduction.mem_maxCompact.1 hx).1 w0
  rw [Reduction.mem_archCompact] at hn
  set M : Matrix (Fin 2) (Fin 2) w0.Completion :=
    ((Reduction.infAt w0 x : GL (Fin 2) w0.Completion) : Matrix (Fin 2) (Fin 2) w0.Completion)
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw0
  have hE : ∀ a b, realPart x a b = e (M a b) := fun a b => rfl
  have hEn : ∀ z, ‖e z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw0).norm_map_of_map_zero
      (map_zero _) z
  have key : ∀ y0 y1 : ℝ, (y0 * realPart x 0 0 + y1 * realPart x 1 0) ^ 2 +
      (y0 * realPart x 0 1 + y1 * realPart x 1 1) ^ 2 = y0 ^ 2 + y1 ^ 2 := by
    intro y0 y1
    have h := hn ![e.symm y0, e.symm y1]
    simp only [Reduction.euclidNorm, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hy : ∀ (y : ℝ) (z : w0.Completion), ‖e.symm y * z‖ = |y| * ‖e z‖ := by
      intro y z
      rw [norm_mul, hEn, ← hEn (e.symm y), RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    have hsum : ∀ j : Fin 2, ‖e.symm y0 * M 0 j + e.symm y1 * M 1 j‖ =
        |y0 * realPart x 0 j + y1 * realPart x 1 j| := by
      intro j
      rw [← hEn, map_add (f := _), map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        hE, hE, Real.norm_eq_abs]
    have hy0 : ‖e.symm y0‖ = |y0| := by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    have hy1 : ‖e.symm y1‖ = |y1| := by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    rw [hsum 0, hsum 1, hy0, hy1, sq_abs, sq_abs, sq_abs, sq_abs] at h
    have := congrArg (· ^ 2) h
    rwa [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at this
  have k10 := key 1 0
  have k01 := key 0 1
  have k11 := key 1 1
  refine ⟨by linear_combination k10, by linear_combination k01, ?_⟩
  linear_combination (k11 - k10 - k01) / 2


end GL2Classical

end

end GroundTheory.Automorphic
end

