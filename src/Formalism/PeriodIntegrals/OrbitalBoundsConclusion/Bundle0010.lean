module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LargeStabilizerInverse.GLeftInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.ChartZeroEqOneOfLongWeylSq
public import Formalism.PeriodIntegrals.Bundle0017
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittSubstitution.CoeffMapMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WhittakerFunctionalDual.StableOfIrreducible
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.WittOf
public import Formalism.PeriodIntegrals.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StabBig
section
theorem stabilizer_large : PI.StabBig := PI.StabBigW.stabBig
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwSandwichOf
section
theorem sandwich_of_chart : PI.SwSand.SandwichOf :=
  PI.SwSandwichOfWork.sandwichOf_of_charts PI.SwSandwichOfWork.normRL PI.SwSandwichOfWork.logG
    PI.SwSandwichOfWork.chartFwd PI.SwSandwichOfWork.chartBwd PI.SwSandwichOfWork.sideB
    PI.SwSandwichOfWork.sideA
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJUnimod
section
theorem unitary_unimodular_right_inv : PI.UJUnimod.UJRightInv :=
  fun n ε => ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst
section
theorem witt_substitution : PI.WfSubst := PI.WfSubstProof.wfSubst
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WhitFunctDual
section
theorem whittaker_functional_dual : PI.WhitFunctDual := PI.WhitFunctDualWork.whitFunctDual_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
section
theorem witt_extension_theorem : PI.WittExtension :=
  PI.Witt.witt_of PI.Witt.one_vector_holds PI.Witt.anisotropic'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ZerosWindow
section
theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI
end

