module

public import Mathlib
public import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0002
public import Formalism.IncomingBounds.Bundle0001

@[expose] public section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

def LevelsChain : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T : ℕ) (e : ℤ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
    (((T : ℝ) * νs ≤ e ∧ ∀ z, ∃ n : ℤ, (ep z : ℝ) * ν z = n) ∨ e = ⌈(T : ℝ) * (νs + 1)⌉) →
      ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z

def LengthBaseChangeLocal : Prop :=
  ∀ (O O₁ Q : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O₁]
    [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra O O₁] [AddCommGroup Q] [Module O Q]
    (ϖ : O) (ϖ₁ : O₁) (u : O₁ˣ) (ε : ℕ), Irreducible ϖ → Irreducible ϖ₁ →
    algebraMap O O₁ ϖ = u * ϖ₁ ^ ε → Module.length O Q ≠ ⊤ →
      Module.length O₁ (TensorProduct O O₁ Q) = ε * Module.length O Q

end Formalism.LatticeBaseChangeAlt
