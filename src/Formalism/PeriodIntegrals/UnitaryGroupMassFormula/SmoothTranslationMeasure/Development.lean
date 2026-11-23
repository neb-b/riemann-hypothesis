module

public import Formalism.PeriodIntegrals.Bundle0005

@[expose] public section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

def MulOnUH {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ ∀ a ∈ UH Hm, ∀ b ∈ UH Hm, σ (a * b) = (σ a).comp (σ b)

section Deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Deriv

end PI.PhMeasCore.UnitaryGroupMassFormula

end
