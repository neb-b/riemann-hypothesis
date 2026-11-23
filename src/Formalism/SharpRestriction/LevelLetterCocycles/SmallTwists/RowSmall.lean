module

public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.RowSmall

open Formalism.BasicNotions NumberField

variable {D : D7}

def sl (D : D7) (l : ℕ) : ℕ := max 1 (D.host.condN.factorization l)

def hB (L : SizeData₂ D) : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t + 2

def abelian₂ (L : SizeData₂ D) (l : ℕ) : ℝ := (sl D l : ℝ) + Real.logb l (2 * hB L) + 1

end Formalism.MainNotions.N.RowSmall

end
