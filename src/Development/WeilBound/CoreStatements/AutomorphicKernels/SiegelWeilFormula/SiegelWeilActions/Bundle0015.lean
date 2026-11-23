module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DMEqDiag
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBUnitary
section
noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} (i₀ : Fin n) (em : Fin k → Fin n)

def cB (u v : Fin k → R) (z : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks (1 + ∑ j, Matrix.single i₀ (em j) (u j)) (Matrix.single i₀ i₀ z) 0 (1 - ∑ j, Matrix.single (em j) i₀ (v j))

variable {i₀ em}

theorem cB_mul (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z : R) : cB i₀ em u v z * cB i₀ em (-u) (-v) (-z) = 1 := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, Matrix.fromBlocks_multiply, Pi.neg_apply, ← Matrix.single_neg,
    Finset.sum_neg_distrib]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, one_mul, mul_one, mul_zero, zero_mul,
      hPP, hQQ, hPZ, hZQ, neg_zero, add_zero, zero_add, sub_zero, neg_neg] <;>
    abel

theorem cB_unitary (hem : ∀ j, em j ≠ i₀) (f : R →+* R) (hf : ∀ a, f (f a) = a) (e : R) (he : e * e = 1)
    (u : Fin k → R) (z : R) (hz : f z = -(e * z)) :
    (cB i₀ em u (fun j => f (u j)) z)ᵀ * kunf.jw n e * (cB i₀ em u (fun j => f (u j)) z).map f = kunf.jw n e := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  have hmap : ∀ M : Matrix (Fin n) (Fin n) R, M.map f = f.mapMatrix M := fun M =>
    (RingHom.mapMatrix_apply f M).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, PositivityTheory.SiegelWeilFormula.kunf.jw, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_sum, Matrix.transpose_single, hmap,
    map_add, map_sub, map_one, map_zero, map_sum]
  simp only [RingHom.mapMatrix_apply, Matrix.map_single, hf, hz]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mul_zero, zero_mul, add_zero]
  · simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_sub, add_mul, one_mul, hQQ, sub_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one]
    congr 1
    simp only [mul_add, sub_mul, one_mul, mul_one, hPP, add_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      mul_sub, sub_mul, one_mul, hPZ, hZQ, sub_zero, Matrix.smul_single, smul_eq_mul, smul_zero]
    rw [← Matrix.single_add, show e * -(e * z) + z = 0 by linear_combination (-z) * he, Matrix.single_zero]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.WMUnitary
section
noncomputable section

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n)

theorem wM_map {S : Type} [CommRing S] (f : R →+* S) (a b : R) : (wM i₀ a b).map f = wM i₀ (f a) (f b) := by
  delta wM
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, map_sub]
  split_ifs <;> simp

theorem wM_blocks (a b : R) : wM i₀ a b = Matrix.fromBlocks (1 - Matrix.single i₀ i₀ 1) (a • Matrix.single i₀ i₀ 1)
    (b • Matrix.single i₀ i₀ 1) (1 - Matrix.single i₀ i₀ 1) := by
  delta wM
  ext (i | i) (j | j) <;>
    simp [Matrix.single_apply, Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem wM_unitary (f : R →+* R) (a b e : R) (h1 : b * e * f a = 1) (h2 : a * f b = e) :
    (wM i₀ a b)ᵀ * kunf.jw n e * (wM i₀ a b).map f = kunf.jw n e := by
  have hjw : kunf.jw n e = Matrix.fromBlocks 0 1 (e • 1) 0 := rfl
  have hEE : Matrix.single i₀ i₀ (1 : R) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hET : (Matrix.single i₀ i₀ (1 : R))ᵀ = Matrix.single i₀ i₀ 1 := Matrix.transpose_single _ _ _
  have h1' : e * b * f a = 1 := by rw [mul_comm e b]; exact h1
  rw [wM_map, wM_blocks, wM_blocks, hjw]
  generalize Matrix.single i₀ i₀ (1 : R) = E at hEE hET ⊢
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hET,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, hEE, sub_self, smul_zero,
    sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · trivial
  · linear_combination (norm := module) h1' • E
  · linear_combination (norm := module) h2 • E
  · trivial
end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

