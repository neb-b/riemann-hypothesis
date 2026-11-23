module

public import Mathlib

@[expose] public section

open MeasureTheory Module Metric Set
open scoped Pointwise

noncomputable section

namespace Formalism.FN

def succMin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) (K : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))}

def MinkowskiIIUpper : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)
        ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ

end Formalism.FN
