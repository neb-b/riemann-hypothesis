module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfF

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLE
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

theorem coordL {n : ℕ} (W : V n → ℂ) (S : Fin n → V n → ℂ) (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0)
    (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => S k z / W z : V n)) 0).det ≠ 0) :
    ∃ L : V n ≃L[ℂ] V n, (∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z) ∧
      (fun z => (WithLp.toLp 2 fun k => S k z / W z : V n) - L z) =o[𝓝 0] fun z => z := by
  classical
  let F : V n → V n := fun z => (WithLp.toLp 2 fun k => S k z / W z : V n)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  have hcomp : ∀ k, DifferentiableAt ℂ (fun y => S k y / W y) 0 :=
    fun k => ((hS k).div hW hW0).differentiableAt
  have hG : DifferentiableAt ℂ (fun z k => S k z / W z) 0 := differentiableAt_pi.2 hcomp
  have hFd : DifferentiableAt ℂ F 0 := e.symm.differentiableAt.comp 0 hG
  have hdet' : LinearMap.det (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) ≠ 0 := hdet
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) hdet').toContinuousLinearEquiv
  have hL : ∀ z, L z = fderiv ℂ F 0 z := fun z => rfl
  refine ⟨L, fun k z => ?_, ?_⟩
  · rw [hL]
    have h1' := ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).hasFDerivAt (x := F 0)).comp (0 : V n) hFd.hasFDerivAt
    have h1 : HasFDerivAt (fun y => S k y / W y)
        ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).comp (fderiv ℂ F 0)) 0 := h1'
    rw [h1.fderiv]
    rfl
  · have h2 := hFd.hasFDerivAt.isLittleO
    have hF0 : F 0 = 0 := by
      apply PiLp.ext
      intro k
      simp [F, hS0]
    simp only [hF0, sub_zero] at h2
    exact h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfG
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def LA (A : ι → Matrix (Fin r) (Fin r) ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun v i := (A i.1 * Mt v i.1) i.2.1 i.2.2
  map_add' v v' := by
    funext i; simp only [Pi.add_apply, Matrix.mul_apply, Mt, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i; simp only [Pi.smul_apply, Matrix.mul_apply, Mt, Matrix.of_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring

def eB (ι : Type*) (r : ℕ) : Ix ι r ≃ Fin r × (ι × Fin r) where
  toFun i := (i.2.1, (i.1, i.2.2))
  invFun j := (j.2.1, j.1, j.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.det (LA A) = ∏ τ, (A τ).det ^ r := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ix ι r)), ← Matrix.det_reindex_self (eB ι r)]
  have hM : Matrix.reindex (eB ι r) (eB ι r)
      (LinearMap.toMatrix (Pi.basisFun ℂ (Ix ι r)) (Pi.basisFun ℂ (Ix ι r)) (LA A)) =
      Matrix.blockDiagonal (fun k : ι × Fin r => A k.1) := by
    ext ⟨a, τ, b⟩ ⟨c, τ', d⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Pi.basisFun_repr, Matrix.blockDiagonal_apply]
    simp only [eB, Equiv.coe_fn_symm_mk, LA, LinearMap.coe_mk, AddHom.coe_mk, Mt, Matrix.mul_apply,
      Matrix.of_apply]
    by_cases h : (τ, b) = (τ', d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [if_pos rfl, Finset.sum_eq_single c]
      · simp
      · intro k _ hk
        simp [Pi.single_apply, hk]
      · simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ((τ, k, b) : Ix ι r) ≠ (τ', c, d) := by
        intro he
        apply h
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨he.1, he.2.2⟩
      simp [Pi.single_apply, this]
  rw [hM, Matrix.det_blockDiagonal, Fintype.prod_prod_type]
  simp [Finset.prod_const]

theorem lintegral_comp_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ τ, (A τ).det ≠ 0)
    {F : (Ix ι r → ℂ) → ENNReal} (hF : Measurable F) :
    ∫⁻ v, F (LA A v) = ENNReal.ofReal (Complex.normSq (∏ τ, (A τ).det ^ r))⁻¹ * ∫⁻ v, F v := by
  have hdet : LinearMap.det ((LA A).restrictScalars ℝ) = Complex.normSq (∏ τ, (A τ).det ^ r) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_LA]
  have hne : LinearMap.det ((LA A).restrictScalars ℝ) ≠ 0 := by
    rw [hdet, Ne, Complex.normSq_eq_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hA τ)
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Ix ι r → ℂ))) hne
  have hmeas : Measurable ((LA A).restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫⁻ v, F (LA A v) = ∫⁻ v, F ((LA A).restrictScalars ℝ v) := rfl
    _ = ∫⁻ v, F v ∂(Measure.map ((LA A).restrictScalars ℝ) volume) :=
        (lintegral_map hF hmeas).symm
    _ = _ := by
        rw [hmap, lintegral_smul_measure, hdet,
          abs_of_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg _)), smul_eq_mul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

