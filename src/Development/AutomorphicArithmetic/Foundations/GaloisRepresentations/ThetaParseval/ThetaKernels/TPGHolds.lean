module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0036
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0100
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0086
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0099
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0082
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TP
open GlobalTheory.ThK.Dbl
theorem tools_holds_k : _root_.UpperTheory.TP.Tools_k :=
  have p1 := _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of_k _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_k _root_.GlobalTheory.ThK.Dbl.frameConj_k _root_.GlobalTheory.ThK.Dbl.finLevel_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
  have l1 := _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k _root_.GlobalTheory.ThK.Dbl.finLevel_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
  have l2 : GlobalTheory.RealLift.LieSecond := PositivityTheory.ThKR.lieSecond2 PositivityTheory.ThKR.localLift_holds PositivityTheory.RL.derEx
  { swFull := _root_.GlobalTheory.ThK.Dbl.swFullX_of_k p1.2 (_root_.GlobalTheory.ThK.Dbl.eisContinues_of_k _root_.PositivityTheory.RgEis.Hd.eisBL_k _root_.GlobalTheory.ThK.Dbl.frameConj_k) l1
    boxSec := l1
    dbl := _root_.GlobalTheory.ThK.Dbl.dblX_k
    stab2 := _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
    cpt := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k
      (PositivityTheory.ThKEst.siegelAll_of UpperTheory.Lit.siegelSetUnitary_of_core) PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
    basic := _root_.PositivityTheory.ThKF0.thetaBasic_k
    polSch := _root_.GlobalTheory.ThK.Dbl.polSch_k
    unfold0 := _root_.GlobalTheory.ThK.Dbl.unfold0_k
    pairEx := _root_.PositivityTheory.ThKG.Tow.pairEx_of_k _root_.PositivityTheory.ThKG.Tow.modelEx_k _root_.PositivityTheory.ThKW.S.weilEx_k
    split := _root_.UpperTheory.TP.splitFree_k
    vacFix := _root_.GlobalTheory.ThK.Dbl.vacFix2_k
    acts := _root_.PositivityTheory.ThKF0.actsEx_k
    lie1 := PositivityTheory.RL.lieFirst l2
    lie2 := l2 }
theorem tLift_holds_k : _root_.UpperTheory.TP.TLift_k := _root_.UpperTheory.TP.tLift_of_tools_k _root_.UpperTheory.TP.tools_holds_k (_root_.GlobalTheory.ThK.Dbl.hgtEx_of_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k)
end UpperTheory.TP
end
