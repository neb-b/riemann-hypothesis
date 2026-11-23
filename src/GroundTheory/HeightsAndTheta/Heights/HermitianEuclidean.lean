module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HermitianSum

@[expose] public section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section RealToFibre

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

variable {σ E}

end RealToFibre

variable [NumberField K]

section General

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

variable (h : HermitianMetric K E)

def RealSpace (_h : HermitianMetric K E) : Type _ := ℝ ⊗[ℤ] E

namespace RealSpace

instance : AddCommGroup (RealSpace h) := inferInstanceAs (AddCommGroup (ℝ ⊗[ℤ] E))

def ofModule : E →+ RealSpace h := (TensorProduct.mk ℤ ℝ E 1).toAddMonoidHom

def lattice : Submodule ℤ (RealSpace h) := LinearMap.range (ofModule h).toIntLinearMap

end RealSpace

end General

end

end GroundTheory.Heights₂.Heights
