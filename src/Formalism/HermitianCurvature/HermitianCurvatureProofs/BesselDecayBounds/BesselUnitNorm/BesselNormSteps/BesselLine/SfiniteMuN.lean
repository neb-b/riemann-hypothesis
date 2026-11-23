module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.PsiMulStar

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

def GrpAll : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), GrpF k r z

def SigAll : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → SigU σ

def PiAll : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)),
    inWb k r z → 0 < Tz k r z → IsHCTypeW k r z u π → PiU z π

def PsiAll : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), inWb k r z → PsiF k r z c

instance sfinite_muN {k r : ℕ} (L : LocBessel k r) : SFinite L.μN := by
  unfold LocBessel.μN haarLie
  infer_instance

end PI.WBL.Cv
