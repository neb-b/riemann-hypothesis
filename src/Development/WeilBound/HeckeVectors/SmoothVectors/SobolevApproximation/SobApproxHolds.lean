module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0007

@[expose] public section

namespace CompanionTheory.D.gk.HC

open Formalism.IndefR.Tow.SobPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sobApprox_holds : SobApprox :=
  sobApprox_of haarExists_holds polyKernel_holds (avgSmooth_of sobChart_holds) avgKFin_holds
    (continuity_of_sobolev_chart sobChart_holds foldCont_holds) (foldBddK_of sobChart_holds)

end CompanionTheory.D.gk.HC
