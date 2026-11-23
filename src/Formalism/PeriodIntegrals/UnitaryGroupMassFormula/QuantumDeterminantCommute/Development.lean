module

public import Formalism.HermitianCurvature.StatementQ

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace QmCapCommW

def CapCongr : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f f' : Mx k r → E), IsOpen D → (∀ g ∈ Glev k r i ∩ D, f g = f' g) →
    ∀ g ∈ Glev k r i ∩ D, EH k r (posL k r i a) (posL k r i b) f g = EH k r (posL k r i a) (posL k r i b) f' g

def QdetCommute : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ u v : ℂ, qdet E u * qdet E v = qdet E v * qdet E u

def CapTransfer : Prop := CapCongr → QdetCommute → EabPres → EabGlLev → CapCommute

end QmCapCommW
