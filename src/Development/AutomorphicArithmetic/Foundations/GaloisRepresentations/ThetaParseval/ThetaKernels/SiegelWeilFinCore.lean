module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0082
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0072
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0067
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0083
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0076
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0074
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0081
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0069
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0092
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0090
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0058
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0091
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcUExS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0094
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0070

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem tTheta_k : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k := _root_.PositivityTheory.SiegelWeilFormula.Tpar.tTheta_of_k (_root_.PositivityTheory.SiegelWeilFormula.tweyl.tthetaComm_k _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij)
theorem tAll_of_k (hW : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k) : _root_.PositivityTheory.SiegelWeilFormula.TAll_k := ⟨_root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij, _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k, hW, _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaAuto_k _root_.GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k⟩
theorem thetaCoef_k : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k := _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaCoef_k _root_.GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k
theorem siegelWeilStd_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k)
    (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) (hH : HolLead) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := by
  have hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds
  have hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
  have hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k := _root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT
  have hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k := _root_.PositivityTheory.SiegelWeilFormula.KSplit.gSplit_of_k hF (_root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_tAll_k hT)
  have hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k := _root_.PositivityTheory.SiegelWeilFormula.Avac.vacK_of_k hT hF hLo hLI (_root_.PositivityTheory.SiegelWeilFormula.KAway.finAct_of_tAll_k hT)
  have hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitK_of_k hT hA _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k hF hKP _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k whitGenLt _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hWE : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k :=
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitEq_of_k hT hA _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k hF hKP _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k whitGenEq _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hWL : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitLow_of_k hVK hT hA hF _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k whitGenLow _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hSt : _root_.PositivityTheory.SiegelWeilFormula.Step_k := _root_.PositivityTheory.SiegelWeilFormula.AStep.stepOf_k hH Holtb.holT hT _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k hA _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k hF (_root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_k hT.1) hLo hLI hGS hPK _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k
    _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k (_root_.PositivityTheory.SiegelWeilFormula.KSing.lamSing_of_k _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.Krd.denseW_k hA) _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k hWL hVK
    (_root_.PositivityTheory.SiegelWeilFormula.Avac.iwaQ_of'_k hT) hCT _root_.PositivityTheory.SiegelWeilFormula.Afc.uEx_k (_root_.PositivityTheory.SiegelWeilFormula.Afc.fcConj_of_k hA) _root_.PositivityTheory.SiegelWeilFormula.Afc.orbRes_k
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.siegelWeilStd_of_k AbsSt.absThm hT _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k hLo hLI hGS (_root_.PositivityTheory.SiegelWeilFormula.KSplit.gIinv_of_k hT hF) hGD hKP hPK _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k hW hWE
    AbsSt.vacuum_generates_polynomials hLD hVK hSt
end PositivityTheory.SiegelWeilFormula.Fin
end
end
