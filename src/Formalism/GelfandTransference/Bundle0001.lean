module

public import Mathlib

@[expose] public section

-- bundled from Formalism.GelfandTransference.EnergyIdentity
section
open Finset

noncomputable section

namespace Formalism.HadamardInequality

def succMin {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : Submodule ℤ E)
    (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ v : Fin i → E, (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ r}

def zdual {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : Submodule ℤ E) :
    Submodule ℤ E where
  carrier := {y | ∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z1, h1⟩ := ha x hx
    obtain ⟨z2, h2⟩ := hb x hx
    exact ⟨z1 + z2, by rw [inner_add_right, h1, h2]; push_cast; ring⟩
  zero_mem' := by intro x _; exact ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha x hx
    obtain ⟨z, h⟩ := ha x hx
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, inner_smul_right, h]; push_cast; ring⟩

def Transference : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℤ E), DiscreteTopology M → Submodule.span ℝ (M : Set E) = ⊤ →
    ∀ i : ℕ, 1 ≤ i → i ≤ Module.finrank ℝ E →
      succMin (zdual M) i * succMin M (Module.finrank ℝ E + 1 - i) ≤
        (Module.finrank ℝ E : ℝ) ^ 2

end Formalism.HadamardInequality
end
end

-- bundled from Formalism.GelfandTransference.GelfandCentral
section
open Finset

noncomputable section

namespace Formalism.HadamardInequality

def GlRel {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

end Formalism.HadamardInequality
end
end

-- bundled from Formalism.GelfandTransference.Statement
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.HadamardInequality




def Hadamard : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ), ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2

def HadamardMax : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) (M : ℝ), (∀ i j, ‖A i j‖ ≤ M) →
    ‖A.det‖ ^ 2 ≤ ((ρ : ℝ) * M ^ 2) ^ ρ

end Formalism.HadamardInequality
end
end

