module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

@[expose] public section

noncomputable section

namespace Formalism.HC

def HasWindows (S : Set ℝ) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ S

theorem HasWindows.mono {S S' : Set ℝ} {la x0 : ℝ} (h : HasWindows S la) (hS : ∀ x ≥ x0, x ∈ S → x ∈ S') :
    HasWindows S' la := by
  intro y
  obtain ⟨Y, hyY, hY⟩ := h (max y x0)
  exact ⟨Y, (le_max_left _ _).trans hyY,
    fun x h1 h2 => hS x ((le_max_right _ _).trans (hyY.trans h1)) (hY x h1 h2)⟩

namespace Level

variable (Λ : Level)

def FormBAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ

def FormB : Prop := ∀ la : ℝ, 1 < la → Λ.FormBAt la

variable {Λ}

end Level

end Formalism.HC

end
