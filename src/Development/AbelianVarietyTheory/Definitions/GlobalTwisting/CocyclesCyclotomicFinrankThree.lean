module

public import Mathlib

@[expose] public section

noncomputable section

namespace GlobalTheory.OrdLoc

variable {G : Type} [Group G] [TopologicalSpace G] (E : Type) [NontriviallyNormedField E]

variable {E}

def Z1 (γ : G →* Eˣ) : Submodule E (G → E) where
  carrier := {c | Continuous c ∧ ∀ g h, c (g * h) = c g + (γ g : E) * c h}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, fun g h => by simp only [Pi.add_apply, ha', hb']; ring⟩
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := by
    rintro t a ⟨ha, ha'⟩
    exact ⟨continuous_const.mul ha, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha']; ring⟩

end OrdLoc
end GlobalTheory
