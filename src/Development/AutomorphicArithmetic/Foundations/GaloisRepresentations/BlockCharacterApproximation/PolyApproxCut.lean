module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002

@[expose] public section

noncomputable section

open Polynomial Finset GlobalTheory.Cong

namespace UpperTheory.Gal.CharacterCongruences

section Approx

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

def PolyApproxAt (ε : ℝ) (θ : J → k) (S : Set (J → k)) : Prop :=
  ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε


end Approx

section Ring

variable (O : Type) [CommRing O] (l N m : ℕ)

end Ring

abbrev Ch (n : ℕ) : Type := Multiplicative (ZMod n) →* ℂˣ

end UpperTheory.Gal.CharacterCongruences

end
