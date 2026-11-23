module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntegralityAtFormsOfAway
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.Bundle0003

@[expose] public section

namespace PI.IntegralAtBasePointLattice

theorem integral_at_t0_lattice : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word), Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u :=
  PI.UnitaryGroupMassFormula.IAT.integrality_at_forms_of_away (fun _ _ T _ _ _ => PI.UnitaryGroupMassFormula.IAT.lattices_away_from_place T)

end PI.IntegralAtBasePointLattice
