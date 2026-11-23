module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionBrInt

@[expose] public section

noncomputable section

namespace PI.WGL

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) (h3 : PI.HwIrred) (h4 : PI.GTBranch)
    (h5 : PI.SchurFock) : PI.GTLower := by
  have hN : Numbers := numbers_dominant_large
  have hX : XiFacts := xi_coefficient_facts
  have hZ : CapelliZ := capelli_scalar_identity
  have hV : ZScalarVanish := scalar_vanishing_criterion
  exact gTLower_of_steps hN hX (ioExists_of h3 h4 hX)
    (ioIntegral_of hZ (liftMod_of h3 h4 hZ hV hN hX) hV)
    (adjointBr_of h3 h5 hN hX) (brIntegral_of h2 h3)

end PI.WGL
