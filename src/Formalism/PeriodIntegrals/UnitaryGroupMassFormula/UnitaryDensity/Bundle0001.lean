module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0008

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Derived
section
open Matrix MvPolynomial
open scoped ComplexOrder

namespace PI.UnitaryDenseWork

end PI.UnitaryDenseWork

open PI.UnitaryDenseWork

theorem unitaryDense_of (h : PI.FramesDense) : PI.UnitaryDense := by
  intro n P hP
  let e : Unit × Fin n × Fin n ≃ Fin n × Fin n := Equiv.punitProd _
  have hR : rename e.symm P = 0 := by
    refine h Unit n (fun _ => 1) (fun _ => Matrix.PosDef.one) (rename e.symm P) ?_
    intro y hy
    rw [eval_rename]
    have h1 := hP (y ()) (by simpa using hy ())
    exact h1
  exact rename_injective _ e.symm.injective (by rw [hR, map_zero])
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.GramStep
section
open Matrix
open scoped ComplexOrder

namespace PI.UD

def SVDStep : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), g.det ≠ 0 →
    ∃ (w v : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      wᴴ * w = 1 ∧ vᴴ * v = 1 ∧ g = w * diagonal d * v

def GramStep : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef →
    ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ * C = G ∧ C.det ≠ 0

end PI.UD
end

