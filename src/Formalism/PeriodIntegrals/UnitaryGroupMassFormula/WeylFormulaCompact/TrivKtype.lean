module

public import Formalism.PeriodIntegrals.Bundle0012

@[expose] public section

open PI PI.UpqRep Matrix

noncomputable section

namespace PI.WeylForKInhab

theorem diag_mem {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  simp only [Kset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    first
      | simp [← Complex.exp_conj, ← Complex.exp_add]
      | (rw [Pi.star_apply, ← Complex.exp_conj, ← Complex.exp_add]
         simp [Complex.conj_ofReal])
      | (rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]
         simp)
  · simp only [Jm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

end PI.WeylForKInhab
