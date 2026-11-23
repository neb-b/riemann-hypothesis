module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0008
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvWt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftFock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftAsm

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionIo
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioExists_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of' h3 h4 hx

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionLift
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem liftMod_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hZ : CapelliZ) (hV : ZScalarVanish)
    (hN : Numbers) (hX : XiFacts) : LiftMod :=
  liftMod_asm hZ hV hN hX equivariant_divisibility equivariant_partial_weight (decomp_of h4 equivariant_last_degree)
    (zComm_of h4 equivariant_divisibility equivariant_partial_weight) (fockDetect_of h3 equivariant_divisibility) tuple_decomposition_formula

end PI.WGL
end
end

