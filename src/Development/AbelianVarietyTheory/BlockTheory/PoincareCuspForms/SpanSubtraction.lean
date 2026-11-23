module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def GapsPairing (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i) ∧
    ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
