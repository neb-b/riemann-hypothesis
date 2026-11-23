module

public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.AnalyticInputs
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014

@[expose] public section

theorem zerosWindow_closed : PI.ZerosWindow :=
  zerosWindow_of chk_lBoundRight chk_zetaBoundRight chk_lInvRight

theorem explicitFormula_closed : PI.ExplicitFormula :=
  explicitFormula_of zerosWindow_closed chk_discFactor chk_discLog chk_lBoundRight chk_zetaBoundRight
    chk_lInvRight
