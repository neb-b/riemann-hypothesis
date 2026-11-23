module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.ModLatticeAbsoluteValue

@[expose] public section

namespace PI.UnitaryGroupMassFormula.BetaModX

theorem betaModX_of_iota (h1 : IotaSurj) (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) :
    PI.ScalPairs.BetaL D u u' :=
  betaModX_of h1 lattice_sub_orthogonal_holds positive_weight_holds mod_lattice_absolute_value D u u'

end PI.UnitaryGroupMassFormula.BetaModX
