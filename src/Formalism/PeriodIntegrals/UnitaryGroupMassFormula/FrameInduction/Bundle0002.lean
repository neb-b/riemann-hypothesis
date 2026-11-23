module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

theorem frame_induction_of (hS : SignStep) (hU : UPos) : GramIndependentSignature := by
  intro k r z z' γ hs hp
  have hdet := det_ne k r z z' γ hs hp
  have hQ := hS k r z z' γ hs hp hdet
  exact ⟨indep_of_det k r z z' γ hdet, hQ, hU k r z z' γ hs hp hdet hQ,
    finrank_Uperp_of_det k r z z' γ hdet⟩

end PI.FrameInd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NonposCount
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

lemma isHerm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    (gramM k r z z' g).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [gramM]
  exact (ggHerm_swap _ (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r) _ _).symm

def PosCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1

def NonposCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // ¬ 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1

end PI.FrameInd
end
end

