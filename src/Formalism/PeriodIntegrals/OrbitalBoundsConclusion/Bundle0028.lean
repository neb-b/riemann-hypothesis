module

public import Formalism.PeriodIntegrals.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootJac
section
theorem amplifier_root_jacobian : PI.AmpRoot.RootJac := PI.AmpRootJacW.rootJac
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTBranch
section
theorem gelfand_tsetlin_branching : PI.GTBranch :=
  PI.WGB.gTBranch_of_steps highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
    PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists
    (PI.WGB.realize_of highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
      PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists)
end

