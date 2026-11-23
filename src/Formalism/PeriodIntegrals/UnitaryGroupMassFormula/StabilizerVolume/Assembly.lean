module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnimodStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabU
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdTestInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unimod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCnt

@[expose] public section

namespace PI.VolStabS.Assembly

open PI.VolStabS

theorem fibPin_closed : FibPin := fibPin_holds

theorem sWeqOm_closed : SWeqOm := sWeqOm_of densFibInf_holds densFibV_holds

theorem sdUniq_closed : SdUniq :=
  sdUniq_of_inf sdTestInf_holds

theorem exOmT_holds : ExOmT :=
  exOmT_of_open (fibInfEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densInf_holds)
    (fibVEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densV_holds) sdUniq_closed restrProd_holds

theorem nuInv_holds : NuInv := nuInv_of_pin detAdm_holds compG_holds fibPin_closed sdUniq_closed

theorem volStabFromSW_of_nuNe (hN : NuNeZero) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of exChar_holds exOmT_holds (exStab_of_nu nuInv_holds nuFin_holds hN)
    exFDStab_holds sWeqOm_closed unfold_holds posTest_holds

theorem volStabFromSW_of_open_dens (hDA : DensAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_nuNe (nuNeZero_of_dens archPos_holds locPos_holds hDA qvSum_holds)

theorem volStabFromSW_of_open_aa (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_dens (densAA_of_open hV hH hI hC)

theorem volStabFromSW_of_open_vic (hV : VolAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_aa hV hensAA_holds hI hC

theorem volStabFromSW_of_open_ic (hI : IdxH) (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_vic volAA_holds hI hC

theorem volStabFromSW_of_cntAA (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_ic idxH_holds hC

theorem volStabFromSW_holds : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_cntAA cntAA_holds

end PI.VolStabS.Assembly
