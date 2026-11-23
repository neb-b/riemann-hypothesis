module

public import Mathlib

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open Module Matrix
open scoped ComplexOrder

def ReducedBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Submodule ℤ E) [DiscreteTopology X] [IsZLattice ℝ X] (M : ℝ)
    (v : Fin (finrank ℝ E) → E), LinearIndependent ℝ v → (∀ i, v i ∈ X) →
    (∀ i, ‖v i‖ ^ 2 / 2 ≤ M) →
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ X,
      (∀ j, ‖(b j : E)‖ ^ 2 / 2 ≤ (finrank ℝ E : ℝ) * M) ∧
      ∀ j, ∀ z ∈ X, |inner ℝ (b j : E) z| ≤ 2 * Real.sqrt (finrank ℝ E) * (‖z‖ ^ 2 / 2)

end ReciprocityTheory.ChartRestriction.G.H1
