module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BZMir.Leib

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure GRep (n : ℕ) where
  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]
  ρ : Representation ℂ (GL (Fin n) k) V

attribute [instance] GRep.acg GRep.mod

variable {k}

def GRep.cast {a b : ℕ} (h : a = b) (π : GRep k a) : GRep k b := h ▸ π

def dpow (n : ℕ) (s : ℝ) : GL (Fin n) k →* ℂˣ := detChar (Fin n) (absPow k (s : ℂ))

def GRep.tw {n : ℕ} (π : GRep k n) (s : ℝ) : GRep k n := ⟨π.V, twist π.ρ (dpow n s)⟩

def GRep.prod {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) : GRep k (r + t) := ⟨_, prod2 rfl π₁.ρ π₂.ρ⟩

def derivB (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → GRep k (n + j) → GRep k n
  | 0, _, π => π
  | j + 1, _, π => ⟨_, GlobalTheory.BZMir.deriv k ψ j π.ρ⟩

variable (k)

end GlobalTheory.BZMir.Leib

end
