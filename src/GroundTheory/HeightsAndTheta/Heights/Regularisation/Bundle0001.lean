module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StPuncturedExpOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def PuncturedExpOrder.Statement : Prop :=
  ∀ (R : ℝ) (ψ : ℂ → ℂ) (k : ℤ) (M : ℝ), 0 < R → DifferentiableOn ℂ ψ (ball (0 : ℂ) R \ {0}) →
    (∀ x ∈ ball (0 : ℂ) R \ {0}, ‖Complex.exp (ψ x) * x ^ k‖ ≤ M) →
    0 ≤ k ∧ ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun x => Complex.exp (ψ x)) (𝓝[≠] 0) (𝓝 c)

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StRiemannSlices
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def RiemannExtensionSlices.Statement : Prop :=
  ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    DifferentiableOn ℂ G (ball (0 : Fin n → ℂ) 1 ∩ {z | ∀ i, z i ≠ 0}) →
    (∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c)) →
    ∃ G' : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ G' (ball (0 : Fin n → ℂ) 1) ∧
      ∀ z ∈ ball (0 : Fin n → ℂ) 1, (∀ i, z i ≠ 0) → G' z = G z

end

end GroundTheory.Heights₂.Heights.Regular
end

