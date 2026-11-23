module

public import Mathlib
public import GroundTheory.AutomorphicForms.PartialDifferential.SobolevInterpolation
public import GroundTheory.AutomorphicForms.Bundle0006

@[expose] public section

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem fourier_char_smul (χ : 𝓢(E, ℂ)) (η ξ : E) :
    𝓕 (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) ξ = (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  rw [Real.fourier_eq, SchwartzMap.fourier_coe, Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, inner_sub_right]
  congr 3; ring

section Kernel

variable (s N : ℝ) (χ : 𝓢(E, ℂ))

variable {s N}

end Kernel

section Identity

variable {s N : ℝ} (χ : 𝓢(E, ℂ))

end Identity


end

end GroundTheory.Automorphic.Sobolev
