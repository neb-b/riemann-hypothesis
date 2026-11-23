module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.BranchFormula

namespace GlobalTheory.KJInf

variable {ι : Type} [Fintype ι] {N n : ℕ}

def BrEqv (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N)
    (sg : ι → DomWeight n) (T : (Frames G → ℂ) →ₗ[ℂ] (Frames G' → ℂ)) : Prop :=
  (∀ Φ ∈ ValC G lam, T Φ ∈ ValC G' sg) ∧
    ∀ (k : ι → Matrix (Fin n) (Fin n) ℂ) (kt : ι → Matrix (Fin N) (Fin N) ℂ), IsUni k → (∀ τ, IsBlock hN (kt τ) (k τ) 1) →
      ∀ Φ ∈ ValC G lam, ∀ Φ' : Frames G → ℂ, (∀ y y', IsTr kt y y' → Φ' y = Φ y') →
        ∀ z z', IsTr k z z' → T Φ' z = T Φ z'

end GlobalTheory.KJInf

end
