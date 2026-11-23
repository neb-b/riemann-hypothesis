module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfHerm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0007

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem tensor_localization : TensLoc := tensLocX_of local_integral_of_substitution

theorem hermitian_approximation : HermApprox :=
  hermitian_approximation_of_parts local_switching_lattice tensor_localization lattices_close_locally wPlace bcU gramOK

theorem unitary_class_mass : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_herm hermitian_approximation

set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.tensor_localization
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass

end PI.UnitaryGroupMassFormula.UJClassMass

end
