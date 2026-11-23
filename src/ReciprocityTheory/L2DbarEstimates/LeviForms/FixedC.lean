module

public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0004

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lp_norm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : Lp ℂ 2 μ)
    (G : α → ℂ) (h : (v : α → ℂ) =ᵐ[μ] G) :
    eLpNorm G 2 μ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [eLpNorm_congr_ae h.symm, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v), ENNReal.rpow_two]

end

end ReciprocityTheory.L2DbarEstimates.I
