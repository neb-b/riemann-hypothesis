module

public import Mathlib
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieB
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Bundle0008

@[expose] public section

noncomputable section

open Complex Matrix Filter Topology
open scoped Real RealInnerProductSpace

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

theorem lie_of_exp_banach {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸]
    [StarModule ℝ 𝔸] (Z K : 𝔸) (h : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) * K * NormedSpace.exp (t • Z) = K) :
    star Z * K + K * Z = 0 := by
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  have hP := (hE.star.mul (hasDerivAt_const (0 : ℝ) K)).mul hE
  have hf : ((fun u : ℝ => star (NormedSpace.exp (u • Z))) * (fun _ : ℝ => K)) *
      (fun u : ℝ => NormedSpace.exp (u • Z)) = fun _ => K := by
    funext u
    simp only [Pi.mul_apply]
    exact h u
  rw [hf] at hP
  have e := hP.unique (hasDerivAt_const (0 : ℝ) K)
  simpa [NormedSpace.exp_zero] using e

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem lie_of_exp {𝕜 ι : Type} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (Z K : Matrix ι ι 𝕜)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * K * NormedSpace.exp (t • Z) = K) : Zᴴ * K + K * Z = 0 := by
  exact @lie_of_exp_banach (Matrix ι ι 𝕜) _ _ _ _ ⟨continuous_id.matrix_conjTranspose⟩ _ Z K h

variable {l : Type} [Fintype l] [DecidableEq l]

theorem sympl_eq (w w' : l ⊕ l → ℝ) : sympl w w' = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ w') := by
  simp [sympl, pPart, qPart, dotProduct, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks_mulVec,
    PiLp.inner_apply, Finset.sum_sub_distrib, Matrix.neg_mulVec, Matrix.one_mulVec, Finset.sum_neg_distrib]
  simp only [mul_comm]
  ring

theorem mem_sp_of (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ w w', sympl (A *ᵥ w) (A *ᵥ w') = sympl w w') :
    A ∈ Matrix.symplecticGroup l ℝ := by
  have key : ∀ v u : l ⊕ l → ℝ, (A *ᵥ v) ⬝ᵥ Matrix.J l ℝ *ᵥ (A *ᵥ u) = v ⬝ᵥ (Aᵀ * Matrix.J l ℝ * A) *ᵥ u := by
    intro v u
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [SymplecticGroup.mem_iff']
  ext i j
  have e := h (Pi.single i 1) (Pi.single j 1)
  rw [sympl_eq, sympl_eq, neg_inj, key] at e
  simpa [Matrix.mulVec_single_one, Pi.single_apply, dotProduct, Matrix.mulVec] using e

theorem mem_lie_of (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  have := lie_of_exp X (Matrix.J l ℝ) fun t => by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact SymplecticGroup.mem_iff'.1 (h t)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  refine (mem_skewAdjointMatricesLieSubalgebra _ _).2 ((mem_skewAdjointMatricesSubmodule _ _).2 ?_)
  show Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X
  rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero, this]

variable {W β : Type} [Fintype W] [DecidableEq W] [Fintype β] [DecidableEq β]

def SG (K : W → Matrix β β ℂ) : Subgroup (W → Matrix β β ℂ)ˣ where
  carrier := {g | star g.1 * K * g.1 = K}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : star a.1 * K * a.1 = K := ha
    have hb' : star b.1 * K * b.1 = K := hb
    show star (a.1 * b.1) * K * (a.1 * b.1) = K
    calc _ = star b.1 * (star a.1 * K * a.1) * b.1 := by simp only [star_mul, mul_assoc]
      _ = K := by rw [ha', hb']
  inv_mem' := fun {a} ha => by
    have ha' : star a.1 * K * a.1 = K := ha
    show star a⁻¹.1 * K * a⁻¹.1 = K
    calc _ = star a⁻¹.1 * (star a.1 * K * a.1) * a⁻¹.1 := by rw [ha']
      _ = star (a.1 * a⁻¹.1) * K * (a.1 * a⁻¹.1) := by simp only [star_mul, mul_assoc]
      _ = K := by simp

def LG (K : W → Matrix β β ℂ) : Submodule ℝ (W → Matrix β β ℂ) where
  carrier := {Z | star Z * K + K * Z = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have ha' : star a * K + K * a = 0 := ha
    have hb' : star b * K + K * b = 0 := hb
    show star (a + b) * K + K * (a + b) = 0
    rw [star_add, add_mul, mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' := fun r a ha => by
    have ha' : star a * K + K * a = 0 := ha
    show star (r • a) * K + K * (r • a) = 0
    rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha', smul_zero]

end PositivityTheory.RL.Up

end
