module

public import Mathlib

@[expose] public section

noncomputable section

namespace PI.QD

open NumberField

def Arith : Prop :=
  ∀ (d : ℕ) (x y : ℚ), Squarefree d → d % 4 = 3 → (∃ u : ℤ, 2 * x = u) →
    (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N) → ∃ a v : ℤ, x = a + v / 2 ∧ y = v / 2

def IntCoeffs : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K) (x y : ℚ), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : K) → IsIntegral ℤ ((x : K) + (y : K) * θ) →
    (∃ u : ℤ, 2 * x = u) ∧ (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N)

def Form : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K), θ ^ 2 = -(d : K) →
    Algebra.adjoin ℚ {θ} = ⊤ → ∀ z : K, ∃ x y : ℚ, z = x + y * θ

end PI.QD

end
