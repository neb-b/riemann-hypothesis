module

public import Mathlib
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.Bundle0011

@[expose] public section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Defs

variable {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gv (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (x : H) : H :=
  ∫ h, Φ (umat h) • τ (umat h) x ∂(muG ε)

def SmoothJ (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) : Prop :=
  SmoothOnH (Jm ε) (fun g => τ g y)

end Defs

def StepGarding : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ x : H, SmoothJ ε τ (gv ε τ Φ x)

def StepDenseW : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ W : Submodule ℂ H, FiniteDimensional ℂ W →
      ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
        (∀ a ∈ Kset ε, ∀ m, Φ (a * m * aᴴ) = Φ m) ∧
        ∀ w ∈ W, ‖gv ε τ Φ w - w‖ ≤ ‖w‖ / 2

end PI.KFinSmoothW
