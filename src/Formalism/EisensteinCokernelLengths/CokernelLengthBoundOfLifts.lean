module

public import Mathlib
public import Formalism.FrobeniusContraction.Bundle0001
public import Formalism.FrobeniusContraction.HighestWeightResidueAvoids

@[expose] public section

noncomputable section

open Classical

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts

open Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.V2

def LenBound2 : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts
