module

public import Formalism.SharpRestriction.InertJacobiLevels.AsmRec

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def ej (R : Ranks) (p : HCParam R) (j : ℕ) : ℝ := if h : j - 1 < R.m then ((p.e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

end Formalism.MainNotions.Inhab

end
