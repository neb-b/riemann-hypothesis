module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSHSec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRingSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRedZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSecFun
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0011

@[expose] public section

namespace UpperTheory.Gal.TranscendenceTraces

theorem ptEx_holds : PtEx := @ptEx_of

theorem chart_holds : Chart := @chart_of

theorem fibFin_holds : FibFin := @fibFin_of @chart_holds

theorem ptCommon_holds : PtCommon := @ptCommon_of

theorem ptOne_holds : PtOne := @ptOne_of @chart_holds

theorem wtExt_holds : WtExt := @wtExt_of @ptOne_holds @chart_holds

theorem wtPt_holds : WtPt := @wtPt_of @wtExt_holds @ptCommon_holds

theorem ptLift_holds : PtLift := @ptLift_of

theorem isolateSpec_holds : IsolateSpec := @isolateSpec_of

theorem isolate_holds : Isolate := @isolate_of @chart_holds @isolateSpec_holds

theorem imageOne_holds : ImageOne := @imageOne_of

theorem genBasic_holds : GenBasic := @genBasic_of

theorem indDesc_holds : IndDesc := @indDesc_of

theorem sHSec_holds : SHSec := @sHSec_of

theorem finSec_holds : FinSec := @finSec_of @sHSec_holds

theorem imageFin_holds : ImageFin := @imageFin_of @imageOne_holds

theorem ringSplit_holds : RingSplit := @ringSplit_of @finSec_holds @indDesc_holds

theorem locFinAff_holds : LocFinAff := @locFinAff_of @chart_holds @ringSplit_holds

theorem locFinGeo_holds : LocFinGeo := @locFinGeo_of @locFinAff_holds

theorem coverOne_holds : CoverOne := @coverOne_of

theorem locFinSec_holds : LocFinSec := @locFinSec_of @coverOne_holds @locFinGeo_holds

theorem wtBC_holds : WtBC := @wtBC_of

theorem invTrans_holds : InvTrans := @invTrans_of

theorem galTrans_holds : GalTrans := @galTrans_of @invTrans_holds

theorem splitField_holds : SplitField := @splitField_of

theorem sumComp_holds : SumComp := @sumComp_of @fibFin_holds

theorem wtComp_holds : WtComp := @wtComp_of @sumComp_holds @fibFin_holds

theorem splitCover_holds : SplitCover := @splitCover_of @splitField_holds @galTrans_holds

theorem wtLin_holds : WtLin := @wtLin_of @fibFin_holds

theorem countEx_holds : CountEx := @countEx_of

theorem countWt_holds : CountWt := @countWt_of @ptEx_holds @ptLift_holds @fibFin_holds

theorem wtCrit_holds : WtCrit := @wtCrit_of @ptEx_holds

theorem wtClopen_holds : WtClopen := @wtClopen_of @wtCrit_holds @fibFin_holds

theorem artSum_holds : ArtSum := @artSum_of

theorem stalkSum_holds : StalkSum := @stalkSum_of @chart_holds @artSum_holds

theorem multSec_holds : MultSec := @multSec_of

theorem multSumPt_holds : MultSumPt := multSumPt_of stalkSum_holds multSec_holds ptLift_holds ptOne_holds fibFin_holds

theorem multBC_holds : MultBC := @multBC_of

theorem multSum_holds : MultSum := @multSum_of @multSumPt_holds @multBC_holds

theorem multOpen_holds : MultOpen := @multOpen_of

theorem wtFlat_holds : WtFlat := wtFlat_of wtClopen_holds multSum_holds multBC_holds multOpen_holds

theorem multPt_holds : MultPt := @multPt_of @wtFlat_holds @wtPt_holds @multBC_holds

theorem normSpec_holds : NormSpec := normSpec_of splitCover_holds countEx_holds countWt_holds multPt_holds ptEx_holds ptLift_holds genBasic_holds

theorem wtPush_holds : WtPush := @wtPush_of @sumComp_holds @fibFin_holds

theorem wtLocal_holds : WtLocal := @wtLocal_of @wtCrit_holds

theorem normAff_holds : NormAff := @normAff_of @chart_holds @normSpec_holds

theorem nwtOpen_holds : NwtOpen := @nwtOpen_of @wtBC_holds @multBC_holds @genBasic_holds

theorem wtVanish_holds : WtVanish := wtVanish_of isolate_holds wtPt_holds ptEx_holds ptLift_holds fibFin_holds

theorem wtUnique_holds : WtUnique := @wtUnique_of @wtVanish_holds @wtLin_holds

theorem nwtAgree_holds : NwtAgree := nwtAgree_of nwtOpen_holds wtUnique_holds genBasic_holds multBC_holds

theorem nwtGlue_holds : NwtGlue := nwtGlue_of nwtAgree_holds wtLocal_holds multBC_holds genBasic_holds

theorem wtNormal_holds : WtNormal := @wtNormal_of @normAff_holds @nwtGlue_holds

theorem wtDegConst_holds : WtDegConst := @wtDegConst_of @ptEx_holds

theorem nmlInt_holds : NmlInt := @nmlInt_of

theorem nmlNoeth_holds : NmlNoeth := @nmlNoeth_of

theorem nmlLoc_holds : NmlLoc := @nmlLoc_of @nmlInt_holds @nmlNoeth_holds

theorem nwtFlat_holds : NwtFlat := nwtFlat_of wtBC_holds wtFlat_holds wtUnique_holds multBC_holds

theorem multEt_holds : MultEt := @multEt_of

theorem multBasic_holds : MultBasic := @multBasic_of @multBC_holds @multOpen_holds @multEt_holds

theorem nwtOfFlat_holds : NwtOfFlat := @nwtOfFlat_of @wtFlat_holds @wtUnique_holds @genBasic_holds

theorem nwtDeg_holds : NwtDeg := nwtDeg_of wtNormal_holds wtDegConst_holds multSum_holds multBC_holds genBasic_holds

theorem funSec_holds : FunSec := @funSec_of

theorem phiEx_holds : PhiEx := @phiEx_of @locFinSec_holds

theorem fL_holds : FL := @fL_of @phiEx_holds

theorem rpBasic_holds : RpBasic := @rpBasic_of

theorem imgBasic_holds : ImgBasic := @imgBasic_of

theorem rpOp_holds : RpOp := @rpOp_of @imgBasic_holds

theorem opEq_holds : OpEq := @opEq_of @fL_holds @rpBasic_holds @rpOp_holds

theorem secFun_holds : SecFun := @secFun_of @ptEx_holds

theorem sumExLoc_holds : SumExLoc := @sumExLoc_of @secFun_holds @funSec_holds @fibFin_holds

theorem sumNat_holds : SumNat := @sumNat_of

theorem ptInj_holds : PtInj := @ptInj_of @ptEx_holds

theorem sumEx_holds : SumEx := @sumEx_of @sumExLoc_holds @sumNat_holds @ptInj_holds

theorem trSum_holds : TrSum := trSum_of sumEx_holds sumNat_holds ptInj_holds fibFin_holds

theorem trChar_holds : TrChar := @trChar_of @fL_holds @opEq_holds @trSum_holds @ptInj_holds

theorem famSemi_holds : FamSemi := @famSemi_of

theorem redZero_holds : RedZero := @redZero_of

theorem trRed_holds (h : GlobalTheory.EtC.A8) : TrRed := trRed_of h trChar_holds trSum_holds opEq_holds famSemi_holds redZero_holds rpBasic_holds rpOp_holds ptInj_holds fibFin_holds

theorem trHl_holds (h : GlobalTheory.EtC.A8) : TrHl := @trHl_of (@trRed_holds h)

theorem famLin_holds : FamLin := @famLin_of @fibFin_holds

theorem trLin_holds : TrLin := trLin_of trChar_holds famLin_holds wtLin_holds rpBasic_holds rpOp_holds

theorem trIdQ_holds (h : GlobalTheory.EtC.A8) : TrIdQ := @trIdQ_of (@trHl_holds h) @trLin_holds @wtLin_holds

theorem famPush_holds : FamPush := @famPush_of @sumComp_holds @fibFin_holds

theorem trPush_holds : TrPush := trPush_of trChar_holds famPush_holds wtPush_holds rpBasic_holds rpOp_holds

theorem trDeg_holds : TrDeg := @trDeg_of @trPush_holds @trLin_holds

theorem trDegQ_holds (h : GlobalTheory.EtC.A8) : TrDegQ := @trDegQ_of (@trHl_holds h) @trDeg_holds

theorem famComp_holds : FamComp := @famComp_of @sumComp_holds @fibFin_holds

theorem trComp_holds : TrComp := trComp_of trChar_holds famComp_holds wtComp_holds rpBasic_holds rpOp_holds

theorem trCompQ_holds (h : GlobalTheory.EtC.A8) : TrCompQ := trCompQ_of (trHl_holds h) trComp_holds wtComp_holds

theorem famBC_holds : FamBC := @famBC_of

theorem trBC_holds : TrBC := trBC_of trChar_holds famBC_holds wtBC_holds rpBasic_holds rpOp_holds

theorem trBCQ_holds (h : GlobalTheory.EtC.A8) : TrBCQ := trBCQ_of (trHl_holds h) trBC_holds wtBC_holds

theorem trRel_holds : TrRel := @trRel_of @trLin_holds @wtLin_holds @wtVanish_holds

theorem corrEq_holds : CorrEq := corrEq_of imageFin_holds trRel_holds trPush_holds wtPush_holds

theorem corrEqQ_holds (h : GlobalTheory.EtC.A8) : CorrEqQ := @corrEqQ_of (@trHl_holds h) @corrEq_holds

theorem cycComp_holds : CycComp := @cycComp_of @fibFin_holds

theorem corrBCQ_holds (h : GlobalTheory.EtC.A8) : CorrBCQ := @corrBCQ_of (@trBCQ_holds h)

theorem corrCompQ_holds (h : GlobalTheory.EtC.A8) : CorrCompQ := corrCompQ_of cycComp_holds wtBC_holds wtComp_holds (trBCQ_holds h) (trCompQ_holds h)

theorem trSplitQ_holds (h : GlobalTheory.EtC.A8) : TrSplitQ := trSplitQ_of (trBCQ_holds h) (corrEqQ_holds h) (trIdQ_holds h) wtLin_holds wtFlat_holds multBasic_holds

theorem corrGraphQ_holds (h : GlobalTheory.EtC.A8) : CorrGraphQ := @corrGraphQ_of (@trIdQ_holds h) @wtLin_holds

theorem weights_holds : Weights := ⟨wtBC_holds, wtComp_holds, wtLin_holds, wtPush_holds, wtPt_holds, wtUnique_holds, wtDegConst_holds,
    multBasic_holds, multSum_holds, wtFlat_holds, wtNormal_holds, nmlLoc_holds, nwtFlat_holds, nwtOfFlat_holds,
    nwtDeg_holds⟩

theorem torsion_holds : Torsion :=
  ⟨@trSum_holds, @trBC_holds, @trComp_holds, @trLin_holds, @trPush_holds, @trDeg_holds, @corrEq_holds⟩

theorem adic_holds (h : GlobalTheory.EtC.A8) : Adic := ⟨trRed_holds h, trHl_holds h, trBCQ_holds h, trCompQ_holds h, trDegQ_holds h, corrEqQ_holds h, corrBCQ_holds h,
    corrCompQ_holds h, corrGraphQ_holds h, trSplitQ_holds h⟩

end UpperTheory.Gal.TranscendenceTraces
