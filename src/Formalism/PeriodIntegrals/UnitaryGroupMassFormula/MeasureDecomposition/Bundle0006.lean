module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstLeftInvMuInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAll
section
namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem place_decomposition_instance : InstDecomp :=
  instDecomp_of (placeDecomp_of exponent_fixed_instance adapted_basis_instance) frame_gram_instance

end PI.ScMuExists.UnitaryGroupMassFormula
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.TargetOfInstDecomp
section
namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem target_of_instDecomp (hd : InstDecomp) : PI.ScMuExists.Target :=
  target_of_steps generic_haar_subgroup (genSemi_of generic_haar_subgroup) generic_weil_representation measure_subFacts
    (genModOne_of generic_haar_subgroup) hd proper_action_instance

end PI.ScMuExists.UnitaryGroupMassFormula
end

