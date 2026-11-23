module

public import Formalism.RealPlaceAnalysis.Bundle0003

@[expose] public section

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

def IsHCParam {n : ℕ} (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)

def lowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoN ε - rhoC ε

def GapAtLeast {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  ∀ a b : Fin n, ε a ≠ ε b → h ≤ |lam a - lam b|

def fdegHC {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|) /
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

def rhoStd (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)

def capP {n : ℕ} (lam : Fin n → ℂ) (Y : ℂ) : ℂ := ∏ s : Fin n, (Y + lam s)

def LowKInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) →
    ∀ a, ∃ m : ℤ, lowK ε lam a = (m : ℝ)

def FdegPos : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), Function.Injective lam → 0 < fdegHC lam

def FdegRatio : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), Function.Injective μ →
    (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) → Function.Injective (μ + Pi.single s 1) →
    fdegHC (μ + Pi.single s 1) / fdegHC μ = ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')

def CapelliHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v = capP (fun s => ν s + (rhoStd n s : ℂ)) Y • v

end Formalism.QuantumDeterminants
