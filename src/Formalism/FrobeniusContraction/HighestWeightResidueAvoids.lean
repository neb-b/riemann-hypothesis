module

public import Formalism.FrobeniusContraction.Bundle0001

@[expose] public section

noncomputable section

open Classical

namespace Formalism.WachCohomologyFacts.V2

open Formalism.WachCohomologyFacts

def sgN (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def InWinN (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 1 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ (h : ℤ) - 1

def ClN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (fun x => ¬ InWinN G h η x)

def ResidueAvoidance (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ ClN G h η U, ∀ m : ℤ, -2 * σ - 2 ≤ m → m ≤ (η : ℤ) + 2 * σ + 3 →
    (((if G then x else (h : ℤ) - x) : ℤ) : ZMod ℓ) ≠ (m : ZMod ℓ)

end Formalism.WachCohomologyFacts.V2
