module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0014

@[expose] public section

namespace PI.LocProdFormulaW

theorem locProdFormula_of (h : PI.ProdFormulaE.ProdFormulaE) : PI.LocProdFormula := by
  intro F E _ _ _ _ _ h2 sig atP M hM x hx
  rw [((h F E sig h2 atP).1 M hM x hx).2, Rat.cast_abs]

end PI.LocProdFormulaW
