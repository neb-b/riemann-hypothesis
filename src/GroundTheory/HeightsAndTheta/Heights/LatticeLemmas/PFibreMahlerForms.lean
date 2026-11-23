module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField TensorProduct ComplexAt

noncomputable section

namespace FibreMahlerForms

section Dual

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]

end Dual

section Mahler

variable {d : ℕ}

end Mahler

section Fibre

variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]

theorem finrank_fibreSpace (h : HermitianMetric F W) (σ : F →+* ℂ) :
    Module.finrank ℂ (FibreSpace h σ) = Module.finrank (𝓞 F) W := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := F) (E := W)
  let b := Module.Basis.mk (linearIndependent_fibreVec h σ hs)
    (LatticeLemmas.span_fibreVec_eq_top h σ hs (Fintype.card_fin _)).ge
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

variable {K : Type} [Field K] [NumberField K] [Algebra F K]

end Fibre

end FibreMahlerForms


end

end GroundTheory.Heights₂.Heights
