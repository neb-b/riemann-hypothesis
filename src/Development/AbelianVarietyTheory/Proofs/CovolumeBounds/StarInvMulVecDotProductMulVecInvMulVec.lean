module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory

section RCLike

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  rwa [trace_mul_cycle, ← star_eq_conjTranspose] at h

theorem re_trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1

omit [Fintype n] in
theorem posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) : B.PosSemidef :=
  (hA.nonneg.trans h).posSemidef

omit [Fintype n] in
theorem posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) : B.PosDef := by
  have := hA.add_posSemidef (le_iff.mp h)
  rwa [add_sub_cancel] at this

theorem conjTranspose_mul_mul_le_of_le {m : Type*} [Finite m] {A B : Matrix n n 𝕜} (h : A ≤ B)
    (C : Matrix n m 𝕜) : Cᴴ * A * C ≤ Cᴴ * B * C := by
  have := (le_iff.mp h).conjTranspose_mul_mul_same C
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this

omit [Fintype n] in
theorem transpose_le_transpose_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  have := (le_iff.mp h).transpose
  rwa [transpose_sub] at this

omit [Fintype n] in
theorem real_smul_le_real_smul_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  have := (le_iff.mp h).smul hc
  rwa [smul_sub] at this

variable [DecidableEq n]

theorem inv_le_inv_of_posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB := posDef_of_le hA h
  have hAi := hA.inv
  let _ := hB.isUnit.invertible
  let _ := hA.isUnit.invertible
  let _ := hAi.isUnit.invertible
  have h1 := PosDef.fromBlocks₁₁ (1 : Matrix n n 𝕜) B hAi
  have h2 := PosDef.fromBlocks₂₂ A⁻¹ (1 : Matrix n n 𝕜) hB
  simp only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, inv_inv_of_invertible] at h1 h2
  exact h2.mp (h1.mpr h)

theorem one_le_det_one_add_of_posSemidef {D : Matrix n n 𝕜} (hD : D.PosSemidef) :
    1 ≤ (1 + D).det := by
  first
  | exact @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | (apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add ..)

theorem det_le_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) :
    A.det ≤ B.det := by
  by_cases h0 : A.det = 0
  · rw [h0]; exact (posSemidef_of_le hA h).det_nonneg
  have hA' := hA.posDef_iff_det_ne_zero.mpr h0
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA'.isStrictlyPositive
  let _ := hC.invertible
  have hD := (le_iff.mp h).conjTranspose_mul_mul_same C⁻¹
  have hB : B = star C * (1 + C⁻¹ᴴ * (B - star C * C) * C⁻¹) * C := by
    have e1 : star C * C⁻¹ᴴ = 1 := by
      rw [star_eq_conjTranspose, ← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1,
      Matrix.one_mul, Matrix.mul_assoc, inv_mul_of_invertible, Matrix.mul_one, add_sub_cancel]
  have h1 := one_le_det_one_add_of_posSemidef hD
  rw [hB, det_mul_right_comm, det_mul (star C * C)]
  exact le_mul_of_one_le_right hA.det_nonneg h1

theorem re_det_le_re_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det :=
  (RCLike.le_iff_re_im.mp (det_le_det_of_posSemidef_of_le hA h)).1

theorem re_det_pos_of_posDef {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det :=
  (RCLike.pos_iff.mp hA.det_pos).1

theorem pow_mul_re_det_le_of_smul_le {B B' : Matrix n n 𝕜} (hB : B.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) (h : c • B ≤ B') :
    c ^ Fintype.card n * RCLike.re B.det ≤ RCLike.re B'.det := by
  have := re_det_le_re_det_of_posSemidef_of_le (hB.smul hc) h
  rwa [RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul] at this

theorem inv_real_smul_of_posDef {B : Matrix n n 𝕜} (hB : B.PosDef) {c : ℝ} (hc : c ≠ 0) :
    (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
  let _ := hB.isUnit.invertible
  apply inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
    inv_mul_of_invertible]

theorem le_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix n n 𝕜) := by
  have hU : (hA.1.eigenvectorUnitary : Matrix n n 𝕜) * star (hA.1.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := Unitary.coe_mul_star_self _
  have h1 : A.trace • (1 : Matrix n n 𝕜) - A = (hA.1.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => A.trace - (hA.1.eigenvalues i : 𝕜)) *
        star (hA.1.eigenvectorUnitary : Matrix n n 𝕜) := by
    rw [← diagonal_sub, ← smul_one_eq_diagonal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
    congr 1
    conv_lhs => rw [hA.1.spectral_theorem]
    rfl
  rw [le_iff, h1]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun i => ?_) _
  have : hA.1.eigenvalues i ≤ ∑ j, hA.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  simp only [Pi.zero_apply, sub_nonneg]
  rw [hA.1.trace_eq_sum_eigenvalues]
  exact_mod_cast this

omit [Fintype n] [DecidableEq n] in
theorem smul_eq_re_smul_of_nonneg {c : 𝕜} (hc : 0 ≤ c) (A : Matrix n n 𝕜) :
    c • A = RCLike.re c • A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  congr 1
  exact (RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2)).symm

theorem le_re_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ RCLike.re A.trace • (1 : Matrix n n 𝕜) := by
  rw [← smul_eq_re_smul_of_nonneg hA.trace_nonneg]
  exact le_trace_smul_one_of_posSemidef hA


section Gram

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

end Gram

theorem inv_smul_one_le_inv_of_le_smul_one {A : Matrix n n 𝕜} (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) (h : A ≤ c • (1 : Matrix n n 𝕜)) : c⁻¹ • (1 : Matrix n n 𝕜) ≤ A⁻¹ := by
  have := inv_le_inv_of_posDef_of_le hA h
  rwa [inv_real_smul_of_posDef PosDef.one hc.ne', inv_one] at this

end RCLike

section Rational

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

open NumberField IsCMField

variable [NumberField K] [IsCMField K]

end Rational

end GlobalTheory
