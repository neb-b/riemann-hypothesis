module

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def minorProd {R : Type u} [CommRing R] {σ : Type} {N0 N1 C : ℕ}
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) : MvPolynomial σ R :=
  ∏ c, (Matrix.of fun (r r' : Fin (p c)) => row ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (I c r')).det

end Formalism.DworkPowerSeriesWeights
