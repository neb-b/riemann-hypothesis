module

public import Mathlib

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

open Module Matrix
open scoped NumberField

def gramConst (d : ℕ) : ℝ := 2 ^ (d * (d - 1))

def RedGramStatement : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (m D : ℝ), A.PosDef → 0 < m →
    (∀ x : Fin d → ℤ, x ≠ 0 → m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ))) →
    A.det ≤ D →
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      (∀ i, (fun l => (e i l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (e i l : ℝ)) ≤
        2 ^ (d * (d - 1)) * D / m ^ (d - 1)) ∧
      ∀ (x : Fin d → ℤ) (i : Fin d), ((e.repr x i : ℤ) : ℝ) ^ 2 ≤
        9 ^ d * ((fun l => (x l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (x l : ℝ))) / m

end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

end
