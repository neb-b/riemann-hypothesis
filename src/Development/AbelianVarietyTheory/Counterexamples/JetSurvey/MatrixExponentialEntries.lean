module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0021

@[expose] public section

open Matrix MeasureTheory
noncomputable section
namespace GlobalTheory.Survey.MatrixExponentialEntries
open PI.UpqRep

abbrev M₁ := Matrix (Fin 1) (Fin 1) ℂ

def chi (m : ℤ) (g : M₁) : ℂ →L[ℂ] ℂ := (g 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ

end GlobalTheory.Survey.MatrixExponentialEntries
