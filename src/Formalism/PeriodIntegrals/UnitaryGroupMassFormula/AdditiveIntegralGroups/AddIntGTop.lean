module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar

@[expose] public section

namespace PI.AddIntG.Wk

theorem addIntG_top : PI.AddIntG.Target := glue_holds_var formalGroupLawExists

end PI.AddIntG.Wk
