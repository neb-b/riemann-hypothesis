module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HermitianDual
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt

noncomputable section

section GaussNorms

variable {L : Type*} [Field L]

end GaussNorms

section Sphere

variable {n : ℕ}

end Sphere

section HeightsOfPoints

variable {F : Type*} [Field F] [NumberField F] {W : Type*} [AddCommGroup W] [Module (𝓞 F) W]

variable {K : Type*} [Field K] [NumberField K] [Algebra F K]

variable [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]

def fibreGen (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W) (x : Fin n → ℂ) :
    FibreSpace h σ :=
  ∑ k, x k • fibreVec h σ (w k)

def fibrePoly (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W)
    (P : MvPolynomial (Fin n) ℂ) (ξ : FibreSpace h σ) : ℂ :=
  eval (Function.invFun (fibreGen h σ w) ξ) P

end HeightsOfPoints

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
