module

public import Mathlib
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

@[expose] public section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open scoped ENNReal ComplexOrder

namespace GlobalTheory.UnitaryExtension

theorem exists_isometry_comp {W V : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (a b : W →ₗ[ℂ] V)
    (h : ∀ x, ‖b x‖ = ‖a x‖) : ∃ u : V →ₗᵢ[ℂ] V, ∀ x, u (a x) = b x := by
  have hk : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← norm_eq_zero, h, hx, norm_zero]
  let l : LinearMap.range a →ₗ[ℂ] V :=
    ((LinearMap.ker a).liftQ b hk) ∘ₗ (a.quotKerEquivRange.symm : LinearMap.range a →ₗ[ℂ] _)
  have hl : ∀ x, l ⟨a x, LinearMap.mem_range_self a x⟩ = b x := by
    intro x
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp
  let L : LinearMap.range a →ₗᵢ[ℂ] V :=
    { toLinearMap := l
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hl, h]; rfl }
  refine ⟨L.extend, fun x => ?_⟩
  have := L.extend_apply ⟨a x, LinearMap.mem_range_self a x⟩
  rw [← hl]
  exact this

theorem exists_unitary_mul_eq {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (Fin n) ι ℂ) (h : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * A = B := by
  have key : ∀ (C : Matrix (Fin n) ι ℂ) (x : EuclideanSpace ℂ ι),
      inner ℂ (Matrix.toEuclideanLin C x) (Matrix.toEuclideanLin C x)
        = inner ℂ x (Matrix.toEuclideanLin (Cᴴ * C) x) := by
    intro C x
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  obtain ⟨u, hu⟩ := exists_isometry_comp (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Matrix.toEuclideanLin A x), key, key, h])
  refine ⟨Matrix.toEuclideanLin.symm u.toLinearMap, ?_, ?_⟩
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := Fin n)).injective
    ext1 x
    apply ext_inner_left ℂ
    intro y
    have e : Matrix.toEuclideanLin ((Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ * Matrix.toEuclideanLin.symm u.toLinearMap) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    simp [Matrix.toLpLin_apply]
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := ι)).injective
    ext1 x
    have e : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap * A) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) (Matrix.toEuclideanLin A x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, LinearEquiv.apply_symm_apply]
    exact hu x

end GlobalTheory.UnitaryExtension
