module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option linter.unusedSectionVars false

namespace SecondKind

namespace UnitaryRecombination

section HS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hsVec (X : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 (fun ij => X ij.1 ij.2)

def hs (X : Matrix ι ι ℂ) : ℝ := ‖hsVec X‖

theorem hs_nonneg (X : Matrix ι ι ℂ) : 0 ≤ hs X := norm_nonneg _

theorem hs_sq (X : Matrix ι ι ℂ) : hs X ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [hs, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]; rfl

def tInner (X Y : Matrix ι ι ℂ) : ℝ := (trace (X * Yᴴ)).re

theorem tInner_self (X : Matrix ι ι ℂ) : tInner X X = hs X ^ 2 := by
  rw [hs_sq, tInner, trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem hs_conjTranspose (X : Matrix ι ι ℂ) : hs Xᴴ = hs X := by
  have h : hs Xᴴ ^ 2 = hs X ^ 2 := by
    rw [hs_sq, hs_sq, Finset.sum_comm]
    simp [conjTranspose_apply]
  exact (sq_eq_sq₀ (hs_nonneg _) (hs_nonneg _)).1 h

theorem opNorm_le_hs (X : Matrix ι ι ℂ) : ‖X‖ ≤ hs X := by
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (hs_nonneg _) fun v => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, hs_sq, EuclideanSpace.norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
  calc ‖∑ j, X i j * (WithLp.ofLp v) j‖ ^ 2 ≤ (∑ j, ‖X i j‖ * ‖(WithLp.ofLp v) j‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ (∑ j, ‖X i j‖ ^ 2) * ∑ j, ‖(WithLp.ofLp v) j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem hs_mul_left_le (A X : Matrix ι ι ℂ) : hs (A * X) ≤ ‖A‖ * hs X := by
  refine (sq_le_sq₀ (hs_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [hs_sq, mul_pow, hs_sq, Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have key := (toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 fun i => X i j)
  rw [l2_opNorm_toEuclideanCLM] at key
  have key2 := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at key2
  convert key2 using 2
  rw [ofLp_toEuclideanCLM]
  simp [mulVec, dotProduct, Matrix.mul_apply]

theorem hs_mul_right_le (X B : Matrix ι ι ℂ) : hs (X * B) ≤ hs X * ‖B‖ := by
  rw [← hs_conjTranspose, conjTranspose_mul, ← hs_conjTranspose X, ← l2_opNorm_conjTranspose B,
    mul_comm]
  exact hs_mul_left_le _ _

end HS

section Inner

variable {f : ℕ} {p q : Fin f → ℕ}

end Inner

section Frame

end Frame

end UnitaryRecombination

namespace UnitaryRecombination

section ExpBound

end ExpBound

section Dim

variable (p q : ℕ)

end Dim

end UnitaryRecombination

namespace UnitaryRecombination

section Places

variable {ι : Type*} [Fintype ι]

variable (F : OrthoFrame)

end Places

end UnitaryRecombination

namespace UnitaryRecombination

section Products

variable (F : OrthoFrame)

end Products

end UnitaryRecombination

end SecondKind

end

end GroundTheory.Heights₂.Theta
