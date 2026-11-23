module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.PhiXFinrankRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.CardFibreCompl

@[expose] public section

namespace PI.DensSplitW

theorem fiberCard_holds : FiberCard := by
  intro K V U _ _ _ _ _ _ _ φ hφ k g
  exact FibreCount.fiber_card φ hφ g

end PI.DensSplitW
