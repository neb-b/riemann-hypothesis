module

public import Formalism.PeriodIntegrals.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStepSubstitution
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealFieldComparison.JmMulApply
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.CcPrEq
public import Formalism.PeriodIntegrals.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamAsm

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgWtHwUnq
section
theorem algebraic_weight_highest_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : PI.AlgWtHwUnq.Stmt L n :=
  fun a τ lam lam' h1 h2 =>
    PI.UnitaryGroupMassFormula.HwConjInf.glue_holds_var PI.UnitaryGroupMassFormula.HwConjInf.density_induction PI.UnitaryGroupMassFormula.HwConjInf.general_linear_reduction L n a τ lam lam' h1 h2
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRealK
section
theorem adelic_compact_real_places : PI.AdBridgeSteps.RealK := PI.UnitaryGroupMassFormula.BridgeRealK.realK
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglTriFactor
section
theorem formal_group_tri_factor : PI.FglTriFactor.Lemma := PI.FglTriFactor.Wk.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodLocStd
section
theorem unimodular_local_standard : PI.UnimodLocStd :=
  PI.UnitaryGroupMassFormula.UnimodLocStd.target_of_key
    (PI.UnitaryGroupMassFormula.UnimodLocStd.keyRep_of_ram
      (PI.UnitaryGroupMassFormula.UnimodLocStd.keyStartRam_of_unit PI.UnitaryGroupMassFormula.UnimodLocStd.unitVecRam))
end

