module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Bundle0001

@[expose] public section

noncomputable section

namespace PIW.HCFdeg

open PI.UpqRep

theorem formal_degree_of_schur_unimodular (hSchur : StSchur) (hBdd : StBdd) (hOrthOf : StOrthOf) (hUni : StUnimod) : StableSubspaceMobius :=
  formal_degree_orthogonality (hOrthOf hSchur hBdd) hUni

end PIW.HCFdeg
