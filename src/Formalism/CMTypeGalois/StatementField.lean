module

public import Mathlib
public import Formalism.Bundle0002

@[expose] public section

open NumberField Ideal Finset
open scoped Pointwise

noncomputable section

namespace Formalism.Q3

def IsMQ {k : ℕ} {E : Type*} [Field E] [Algebra ℚ E] (a : Fin k → ℤ) (α : Fin k → E) : Prop :=
  (∀ i, α i ^ 2 = (a i : E)) ∧ IntermediateField.adjoin ℚ (Set.range α) = ⊤


open Classical in
def galSign {k : ℕ} {E : Type*} [Field E] [Algebra ℚ E] (α : Fin k → E) (σ : Gal(E/ℚ)) :
    Fin k → ℤˣ :=
  by
    classical
    exact fun i => if σ (α i) = α i then 1 else -1

def MQGalois : Prop :=
  ∀ (k : ℕ) (E : Type) [Field E] [NumberField E] (a : Fin k → ℤ) (α : Fin k → E),
    IsMQ a α → (∀ i, a i ≠ 0) →
    IsGalois ℚ E ∧
    (∀ (σ : Gal(E/ℚ)) (i : Fin k), σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i) ∧
    (∀ σ τ : Gal(E/ℚ), galSign α (σ * τ) = galSign α σ * galSign α τ) ∧
    Function.Injective (galSign α)

def MQKummer : Prop :=
  ∀ (k : ℕ) (E : Type) [Field E] [NumberField E] (a : Fin k → ℤ) (α : Fin k → E),
    IsMQ a α → (∀ S : Finset (Fin k), S.Nonempty → ¬ IsSquare (∏ i ∈ S, (a i : ℚ))) →
    Module.finrank ℚ E = 2 ^ k ∧ Function.Bijective (galSign α) ∧
    ∀ d : ℚ, IsSquare (algebraMap ℚ E d) ↔
      ∃ S : Finset (Fin k), IsSquare (d * ∏ i ∈ S, (a i : ℚ))


end Formalism.Q3
