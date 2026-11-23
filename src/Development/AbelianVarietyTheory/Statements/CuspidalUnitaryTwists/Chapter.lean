module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

open UpperTheory.V.Af

def Bridge : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (k m n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ m)], 3 ≤ k → Odd k → 1 ≤ m → ∀ (h : m ≤ n)
    (ζ : K), IsPrimitiveRoot ζ (l ^ n) → ∀ ψ : DirichletCharacter K (l ^ m), ψ.IsPrimitive →
    ∀ (b₁ b₂ u v : ℤ → K) (f₁ f₂ : ZMod (l ^ n) → K) (c d : (ZMod (l ^ n))ˣ),
      (∀ x : ℤ, b₁ ((l : ℤ) ^ (n - m) * x) = u x) → (∀ x : ℤ, b₂ ((l : ℤ) ^ (n - m) * x) = v x) →
      (∀ x, u (-x) = ψ (-1) * u x) → (∀ x, v (-x) = -ψ (-1) * v x) → ∀ s : ℕ,
      -((l : K) ^ (n * k) / (l : K) ^ (n * 4)) *
        ∑ γ : ((ZMod (l ^ n))ˣ × (ZMod (l ^ n))ˣ) × ZMod (l ^ n) × ZMod (l ^ n),
          ψ ((((γ.1.1 : ZMod (l ^ n)) * γ.2.2 - (γ.1.2 : ZMod (l ^ n)) * γ.2.1).val : ℕ) : ZMod (l ^ m)) *
            mul (Fser (k - 1) (l ^ n) ζ b₁ (f₁ (c * γ.1.1)) (c * γ.1.1) (c * γ.2.1))
              (Fser 1 (l ^ n) ζ b₂ (f₂ (d * γ.1.2)) (d * γ.1.2) (d * γ.2.2)) s =
      if l ^ n ∣ s then -4 * ((l : K) ^ m)⁻¹ * (∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)) *
        ψ⁻¹ ((((c * d : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val : ℕ) : ZMod (l ^ m)) *
          (Uo l)^[m] (Zs k l u v (quo ψ)) (s / l ^ n) else 0

end GlobalTheory.EisM

end
