module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiOfClosedTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoreUHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ZeroAp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.WeilPhi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TraceEqNextCoeff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.PowTrHolds

@[expose] public section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem ClosedTr_holds : ClosedTr :=
  closedTr_of coverJ_holds frEx_holds
    (opEx_holds (secU_holds coreU_holds) invQ_holds invU_holds (linkZ_holds linkA_holds (linkQ_holds zeroAp_holds linkRec_holds))
      linkOp_holds fixW_holds opOne_holds)
    fixOf_holds
    (tie_holds (tieRep_holds trLin_holds coordEx_holds coordWD_holds colInv_holds weilPhi_holds testTr_holds))
    (trLim_holds (trStep_holds (func_holds intBasis_holds) trId_holds))

theorem congPhi_holds : GlobalTheory.CongPhi.ClosedPhi := congPhi_of_closedTr ClosedTr_holds powTr_holds

end UpperTheory.Gal.ClosedPhiFromClosedTrace
