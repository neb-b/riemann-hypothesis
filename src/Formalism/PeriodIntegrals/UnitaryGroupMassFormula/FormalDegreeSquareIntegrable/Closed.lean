module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Partial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Unimod

@[expose] public section

noncomputable section

namespace PIW.HCFdeg

theorem formal_degree_abstract_form : StableSubspaceMobius := formal_degree_of_schur_unimodular stSchur stBdd stOrthOf stUnimod

end PIW.HCFdeg
