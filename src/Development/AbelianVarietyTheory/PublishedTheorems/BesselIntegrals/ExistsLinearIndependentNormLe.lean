module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

@[expose] public section

noncomputable section

open Module Submodule

namespace GlobalTheory.Published

def SuccMinTransference : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ), 1 ≤ i → i ≤ n → succMin L i * succMin (dualLattice L) (n - i + 1) ≤ n

namespace SuccMinTransference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end SuccMinTransference

end GlobalTheory.Published
