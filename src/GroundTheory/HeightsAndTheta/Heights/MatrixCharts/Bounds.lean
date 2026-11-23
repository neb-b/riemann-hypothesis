module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix
open scoped ComplexOrder

noncomputable section

variable (D : PeriodChartData)

theorem log_inv_sq_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ Real.log (‖w‖ ^ 2)⁻¹ := by
  rw [Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg w) hw.le))

theorem injective_of_rank {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    Function.Injective F.mulVec := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin F)
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank ℂ (LinearMap.ker F.mulVecLin) = 0 := by
    unfold Matrix.rank at h; omega
  have h3 : LinearMap.ker F.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h2
  exact LinearMap.ker_eq_bot.mp h3

theorem gram_posDef {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    (Fᴴ * F).PosDef :=
  PosDef.conjTranspose_mul_self F (injective_of_rank F h)

end

end GroundTheory.Heights₂.Heights.MCBounds
