module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo TensorProduct

section Pullback

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem one_tmul_smul (s : Ω) (v : E) :
    (1 : Ω') ⊗ₜ[Ω] (s • v) = algebraMap Ω Ω' s • ((1 : Ω') ⊗ₜ[Ω] v) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul,
    mul_one]

variable {r : ℕ}

end Pullback

end GroundTheory.Heights₂.Heights
