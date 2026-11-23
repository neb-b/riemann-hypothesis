module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.Bundle0001

@[expose] public section

noncomputable section

namespace PI.AlgValsFin.W

theorem torsUnits (L : Type) [Field L] [NumberField L] : TorsUnits L :=
  torsUnits_of_nbhd L fun W hW h1 => exists_nbhd W hW h1

theorem algValsFin_main (L : Type) [Field L] [NumberField L] : AlgValsFin L :=
  algValsFin_of_tors L (torsUnits L)

end PI.AlgValsFin.W
