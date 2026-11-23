module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0020

@[expose] public section

noncomputable section

open NumberField Matrix
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC

def nsq {n : ℕ} (w : Fin n → ℂ) : ℝ := ∑ i, ‖w i‖ ^ 2

def LatIs : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ Λ : Submodule (𝓞 I.E) (Fin I.n → I.E), Λ.FG ∧
    Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤ ∧ Size.latSet I x = (Λ : Set (Fin I.n → I.E))

def DetMono : Prop :=
  ∀ (n j : ℕ) (C : Matrix (Fin n) (Fin j) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (κ : ℝ), 0 ≤ κ →
    (∀ w : Fin n → ℂ, nsq (M *ᵥ w) ≤ κ * nsq w) →
    0 ≤ ((Cᴴ * C).det).re ∧ (((M * C)ᴴ * (M * C)).det).re ≤ κ ^ j * ((Cᴴ * C).det).re

def NormProd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (m : I.E), ∏ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = |((Algebra.norm ℚ m : ℚ) : ℝ)|

end PI.UnitaryGroupMassFormula.LSC
