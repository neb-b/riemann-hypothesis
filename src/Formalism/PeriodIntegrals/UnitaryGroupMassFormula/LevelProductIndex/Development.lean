module

public import Mathlib
public import Formalism.SatakeDualWeyl.Bundle0001

@[expose] public section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

def PLGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (O : Subring R) (n k : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (m : Fin k → Fin n → E),
    (∀ i, m i ∈ Lb) → (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) →
    ∀ y : Fin n → E ⊗[F] R,
      y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Lb ↔
        ∃ a : Fin k → R, (∀ i, a i ∈ O) ∧ y = fun j => ∑ i, m i j ⊗ₜ[F] a i

end PI.LPI
