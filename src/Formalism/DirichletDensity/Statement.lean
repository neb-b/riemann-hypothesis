module

public import Mathlib
public import Formalism.CMTypeGalois.StatementField

@[expose] public section

open NumberField Ideal Filter Topology Finset Formalism.Q3

noncomputable section

namespace Formalism.HF

def LogDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ =>
      (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n))
    (𝓝[>] 1) (𝓝 δ)

def QuadDiscr : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K),
    x ^ 2 = (a : K) → IntermediateField.adjoin ℚ {x} = ⊤ → Squarefree a → a % 4 = 1 →
    discr K = a

def MQDiscr : Prop :=
  ∀ (k : ℕ) (q : Fin k → ℕ), 1 ≤ k → (∀ i, (q i).Prime ∧ q i % 4 = 3) → Function.Injective q →
  ∀ (E : Type) [Field E] [NumberField E] (α : Fin k → E), IsMQ (fun i => -(q i : ℤ)) α →
    discr E = (-1) ^ (2 ^ (k - 1)) * ∏ i, (q i : ℤ) ^ (2 ^ (k - 1))

def APLogDensity : Prop :=
  ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
    LogDensity {p : ℕ | (p : ZMod N) = a} (1 / (N.totient : ℝ))

end Formalism.HF
