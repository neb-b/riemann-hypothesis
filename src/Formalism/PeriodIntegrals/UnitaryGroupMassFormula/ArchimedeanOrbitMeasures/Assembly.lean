module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UniInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittNearP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsOrthonormalPerp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamDer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousThetaInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensEx

@[expose] public section

namespace PI.AprimeInfAsm

open PI.AprimeInfW

theorem aprimeInf_of_good (hC : MassDataMassesW.HinfCompact) (hG : GoodChartEx) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  have hJ : JacOneC := jacOneC_of_charts kPos_holds unimodInf_holds wittNear_holds hG
  aprimeInf_of_leaves exInf_holds
    (pushInf_of_pushLFin_of_orbUniq_of_constTest (pushLFin_of_compact hC) (orbUniq_of_compact hC)
      (constTest_of_polar_compact
        (polar_local_of_fibres kPos_holds gramMeas_holds (fibOrbAt_of_compact hC) (pushCont_of_compact hC) hJ) hC))
    (weilInf_of (htotInf_of (hinfFin_of hC))) hC

theorem aprimeInf_of_std (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hT : TupStd) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_good hC (goodChartEx_of_witt linIndW_holds perpPosV wittLin_holds hG hT)

theorem lamDet_of_open (hN : NuBridge) (hP : PlaceJacAll) : LamDet :=
  lamDet_of betaIso_holds muBridge_holds hN dKForm_holds rowsZ_holds detT_holds hP

theorem aprimeInf_of_grp (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hN : NuBridge) (hP : PlaceJacAll) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_std hC hG (tupStd_of_sm kapSm_holds (lamDet_of_open hN hP))

end PI.AprimeInfAsm
