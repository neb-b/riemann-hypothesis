module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRankN
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPairCalc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTorsFree
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0030
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MQuasiInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProdHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0003

@[expose] public section

namespace UpperTheory.Gal.crystallineComparison.Mod

theorem wModEx_holds  : WModEx := wModEx_of
theorem valPtsX_holds  : ValPtsX := valPtsX_of
theorem wVal_holds  : WVal := wVal_of valPtsX_holds
theorem rankN_holds  : RankN := rankN_of wVal_holds
theorem secCard_holds  : SecCard := secCard_of
theorem objTri_holds  : ObjTri := objTri_of
theorem pairCalc_holds  : PairCalc := pairCalc_of
theorem pullIsog_holds  : PullIsog := pullIsog_of
theorem pullKer_holds  : PullKer := pullKer_of
theorem pulledEx_holds  : PulledEx := pulledEx_of objTri_holds pullIsog_holds pullKer_holds
theorem pulledRead_holds  : PulledRead := pulledRead_of pullKer_holds
theorem uElt_holds  : UElt := uElt_of
theorem divC_holds  : DivC := divC_of
theorem torsFree_holds  : TorsFree := torsFree_of divC_holds
theorem adjoint_holds  : Adjoint := adjoint_of pairCalc_holds torsFree_holds
theorem kerFromU_holds  : KerFromU := kerFromU_of uElt_holds pairCalc_holds adjoint_holds divC_holds
theorem isoOfKer_holds  : IsoOfKer := isoOfKer_of pairCalc_holds adjoint_holds divC_holds torsFree_holds
theorem secInj_holds  : SecInj := secInj_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds
theorem constSub_holds  : ConstSub := constSub_of
theorem oMod_holds  : OMod := oMod_of
theorem secSurj_holds (h4 : QuotObj) : SecSurj := secSurj_of constSub_holds oMod_holds h4 objTri_holds pullKer_holds
theorem secEquiv_holds (h4 : QuotObj) : SecEquiv := secEquiv_of wVal_holds rankN_holds valPtsX_holds secCard_holds secInj_holds (secSurj_holds h4)
theorem grCard_holds  : GrCard := grCard_of
theorem powExt_holds  : PowExt := powExt_of
theorem genDown_holds  : GenDown := genDown_of
theorem resClosed_holds  : ResClosed := resClosed_of
theorem ordReadOf_holds  : OrdReadOf := ordReadOf_of countIn_of countOut_of
theorem algOf_holds  : AlgOf := algOf_of
theorem liftPt_holds  : LiftPt := liftPt_of
theorem liftFF_holds  : LiftFF := liftFF_of algOf_holds liftPt_holds
theorem lineC_holds  : LineC := lineC_of rankN_holds liftFF_holds
theorem kerU_holds  : KerU := kerU_of uElt_holds
theorem fFRead_holds  : FFRead := fFRead_of algOf_holds
theorem kerRead_holds  : KerRead := kerRead_of kerU_holds fFRead_holds liftFF_holds pullKer_holds wVal_holds
theorem redPts_holds  : RedPts := redPts_of
theorem killLocal_holds  : KillLocal := killLocal_of
theorem splitAlg_holds  : SplitAlg := splitAlg_of
theorem infE_holds  : InfE := infE_of splitAlg_holds
theorem sameE_holds  : SameE := sameE_of killLocal_holds infE_holds
theorem imgEq_holds  : ImgEq := imgEq_of objTri_holds
theorem caseE_holds  : CaseE := caseE_of sameE_holds kerU_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
theorem ringHomog_holds  : RingHomog := ringHomog_of
theorem cotanOne_holds  : CotanOne := cotanOne_of
theorem chainLoc_holds  : ChainLoc := chainLoc_of
theorem chainRing_holds  : ChainRing := chainRing_of chainLoc_holds
theorem repHomog_holds  : RepHomog := repHomog_of
theorem frobRing_holds  : FrobRing := frobRing_of
theorem infW_holds  : InfW := infW_of ringHomog_holds cotanOne_holds chainRing_holds repHomog_holds frobRing_holds
theorem frobPass_holds  : FrobPass := frobPass_of infE_holds
theorem repOfFF_holds  : RepOfFF := repOfFF_of algOf_holds
theorem tanOne_holds  : TanOne := tanOne_of uElt_holds
theorem sameW_holds  : SameW := sameW_of killLocal_holds infW_holds frobPass_holds kerU_holds repOfFF_holds tanOne_holds
theorem frobHom_holds  : FrobHom := frobHom_of
theorem frobFin_holds  : FrobFin := frobFin_of
theorem picFrob_holds  : PicFrob := picFrob_of
theorem quasiInv_holds  : QuasiInv := quasiInv_of pairCalc_holds divC_holds
theorem frobIsog_holds  : FrobIsog := frobIsog_of frobHom_holds frobFin_holds picFrob_holds quasiInv_holds
theorem isogComp_holds  : IsogComp := isogComp_of pairCalc_holds
theorem caseW_holds  : CaseW := caseW_of sameW_holds frobIsog_holds isogComp_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
theorem eW_holds (h4 : QuotObj) : EW := ew_of wModEx_holds rankN_holds lineC_holds (secEquiv_holds h4) kerRead_holds redPts_holds countIn_of pulledEx_holds caseE_holds caseW_holds
theorem corrBC_holds (h4 : QuotObj) : CorrBC := corrBC_of wModEx_holds rankN_holds (secEquiv_holds h4) grCard_holds
theorem ordEmb_holds (h3 : OrdGen) (h4 : QuotObj) : OrdEmb := ordEmb_of h3 genDown_holds resClosed_holds ordReadOf_holds (eW_holds h4)
theorem levPull_holds  : LevPull := levPull_of pullKer_holds
theorem etInj_holds  : EtInj := etInj_of objTri_holds levPull_holds
theorem ordKSE_holds (h3 : OrdGen) (h4 : QuotObj) : OrdKSE := ordKSE_of (corrBC_holds h4) (ordEmb_holds h3 h4) powExt_holds etInj_holds
theorem tjExF_holds (h1 : EsNorm) (h2 : EsGen) : TjExF := tjExF_of h1 h2 objTri_holds pullIsog_holds pullKer_holds
theorem uKerW_holds  : UKerW := uKerW_of kerU_holds pullKer_holds
theorem idealSplit_holds  : IdealSplit := idealSplit_of
theorem levPush_holds  : LevPush := levPush_of idealSplit_holds
theorem tjEEx_holds  : TjEEx := tjEEx_of objTri_holds pulledEx_holds pullKer_holds uKerW_holds levPull_holds levPush_holds
theorem congKS_holds (h1 : EsNorm) (h2 : EsGen) (h3 : OrdGen) (h4 : QuotObj) : CongKS :=
  congKS_of (tjExF_holds h1 h2) tjEEx_holds (ordKSE_holds h3 h4) ptIdOfOrd_holds

end UpperTheory.Gal.crystallineComparison.Mod
