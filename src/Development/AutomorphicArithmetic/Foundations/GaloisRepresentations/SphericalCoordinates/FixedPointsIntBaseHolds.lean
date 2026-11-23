module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpolyHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplexModelPointsOfGenericFiberEmbedding
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFApprox
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPFrameEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkPerf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PJStruct
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTypeIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.TTSymmApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRDicEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PWitOfAd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLevelChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.FixZOf

@[expose] public section

namespace UpperTheory.Gal.W2

theorem ModelEx_holds : ModelEx := GlobalTheory.UPel.HT.model_nonempty

theorem GenCmp_holds : GenCmp := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre

theorem GenPts_holds : GenPts := UpperTheory.Cb.complexModel_points_of_genericFiber_embedding

theorem EmbAll_holds : EmbAll := embAll_of

theorem FTrace_holds : FTrace := fTrace_of EmbAll_holds

theorem FInt_holds : FInt := fInt_of EmbAll_holds

theorem FApprox_holds : FApprox := fApprox_of EmbAll_holds

theorem TrDual_holds : TrDual := trDual_of

theorem MemDual_holds : MemDual := memDual_of TrDual_holds

theorem KpMem_holds : KpMem := kpMem_of

theorem LocLat_holds : LocLat := locLat_of

theorem OOnto_holds : OOnto := oOnto_of

theorem FMat_holds : FMat := fMat_of

theorem FForm_holds : FForm := fForm_of

theorem SN_holds : SN := sN_of

theorem PFrameEx_holds : PFrameEx := pFrameEx_of FMat_holds FForm_holds SN_holds FTrace_holds FInt_holds FApprox_holds

theorem PLatOf_holds : PLatOf := pLatOf_of

theorem PkLat_holds : PkLat := pkLat_of OOnto_holds MemDual_holds PLatOf_holds

theorem PkEquiv_holds : PkEquiv := pkEquiv_of

theorem PkPerf_holds : PkPerf := pkPerf_of MemDual_holds

theorem PkInj_holds : PkInj := pkInj_of MemDual_holds EmbAll_holds

theorem PkOnto_holds : PkOnto := pkOnto_of LocLat_holds FApprox_holds FInt_holds PkLat_holds PkPerf_holds OOnto_holds

theorem ArchSpan_holds : ArchSpan := archSpan_of

theorem ArchEx_holds : ArchEx := archEx_of FMat_holds FForm_holds SN_holds ArchSpan_holds

theorem SigB_holds : SigB := sigB_of

theorem PerExt_holds : PerExt := perExt_of

theorem JStruct_holds : JStruct := jStruct_of ArchSpan_holds

theorem JLine_holds : JLine := jLine_of

theorem HermOfJ_holds : HermOfJ := hermOfJ_of

theorem LineBasis_holds : LineBasis := lineBasis_of

theorem PlaceT_holds : PlaceT := placeT_of

theorem TypeIso_holds : TypeIso := typeIso_of SimDiag_holds ExtendEmb_holds TypeCount_holds PlaceT_holds

theorem RPer_holds : RPer := rPer_of SigB_holds LineBasis_holds TypeIso_holds HermOfJ_holds PlaceT_holds

theorem RDicEx_holds : RDicEx := rDicEx_of ArchEx_holds SigB_holds PerExt_holds JStruct_holds JLine_holds RPer_holds PlaceT_holds

theorem RhoSig_holds : RhoSig := rhoSig_of

theorem BaseC_holds : BaseC := baseC_of

theorem GFine_holds : GFine := gFine_of

theorem GUnif_holds : GUnif := gUnif_of ModelEx_holds GenCmp_holds GenPts_holds BaseC_holds GFine_holds

theorem SheetOf_holds : SheetOf := sheetOf_of

theorem FixFinite_holds : FixFinite := fixFinite_of

theorem RdAct_holds : RdAct := rdAct_of

theorem RdForm_holds : RdForm := rdForm_of

theorem RdDense_holds : RdDense := rdDense_of

theorem AdCore_holds : AdCore := adCore_of

theorem AdOfWit_holds : AdOfWit := adOfWit_of AdCore_holds

theorem WitOfAd_holds : WitOfAd := witOfAd_of RdForm_holds RdDense_holds RdAct_holds

theorem CoordKN_holds : CoordKN := coordKN_of RdDense_holds

theorem PlacePer_holds : PlacePer := placePer_of

theorem PlaceLoc_holds : PlaceLoc := placeLoc_of

theorem LatForm_holds : LatForm := latForm_of

theorem ClsScalar_holds : ClsScalar := clsScalar_of

theorem ActY_holds : ActY := actY_of

theorem LatIso_holds : LatIso := latIso_of RdAct_holds CoordKN_holds ClsScalar_holds ActY_holds

theorem CoordMove_holds : CoordMove := coordMove_of

theorem PlaceEx_holds : PlaceEx := placeEx_of AdCore_holds LatForm_holds

theorem CoordEx_holds : CoordEx := coordEx_of PlaceEx_holds AdOfWit_holds PlaceLoc_holds PlacePer_holds

theorem CoordOcc_holds : CoordOcc := coordOcc_of WitOfAd_holds PlacePer_holds

theorem CoordIso_holds : CoordIso := coordIso_of LatForm_holds LatIso_holds ActY_holds

theorem UnifG_holds : UnifG := unifG_of CoordEx_holds CoordOcc_holds CoordIso_holds CoordMove_holds

theorem Rigid_holds : Rigid := rigid_of

theorem FixLine_holds : FixLine := fixLine_of ActY_holds

theorem StabTriv_holds : StabTriv := stabTriv_of CoordOcc_holds LatIso_holds FixLine_holds Rigid_holds

theorem IsogForm_holds : IsogForm := isogForm_of RdForm_holds

theorem IsogCoord_holds : IsogCoord := isogCoord_of AdOfWit_holds CoordKN_holds IsogForm_holds RdDense_holds

theorem IntMult_holds : IntMult := intMult_of

theorem RegSep_holds : RegSep := regSep_of

theorem InvMin_holds : InvMin := invMin_of

theorem MinBridge_holds : MinBridge := minBridge_of

theorem EigSame_holds : EigSame := eigSame_of

theorem SumPts_holds : SumPts := sumPts_of EigSame_holds

theorem LevelChange_holds : LevelChange := levelChange_of EigSame_holds

theorem TateWit_holds : TateWit := tateWit_of

theorem IsogAt_holds : IsogAt := isogAt_of TateWit_holds PerLin_holds

theorem HeckeCoord_holds : HeckeCoord := heckeCoord_of IsogAt_holds IsogCoord_holds

theorem OneAt_holds : OneAt := oneAt_of HeckeCoord_holds LatIso_holds

theorem FixFwd_holds : FixFwd := fixFwd_of HeckeCoord_holds OneAt_holds LatForm_holds LatIso_holds FixLine_holds ActY_holds

theorem FixGa_holds : FixGa := fixGa_of HeckeCoord_holds LatIso_holds FixLine_holds ActY_holds IntMult_holds

theorem FixEq_holds : FixEq := fixEq_of HeckeCoord_holds OneAt_holds LatIso_holds

theorem PwOver_holds : PwOver := pwOver_of

theorem PowCorr_holds : PowCorr := powCorr_of PwOver_holds PtFibre_holds

theorem PowSm_holds : PowSm := powSm_of

theorem FixLoc_holds : FixLoc := fixLoc_of SheetOf_holds FixGa_holds FixEq_holds OneAt_holds PowCorr_holds CspDim_holds AdExists_holds EigTop_holds LocSum_holds RegSep_holds InvMin_holds MinBridge_holds CorrChart_holds PtFibre_holds

theorem PDicEx_holds : PDicEx := pkTop_of PFrameEx_holds PkLat_holds PkEquiv_holds PkPerf_holds PkInj_holds PkOnto_holds KpMem_holds

theorem fixedPoints_int_base_holds : HeckeFixedPointCMCycleClass := fixedPoints_integral_base_of_uniformisation RhoSig_holds GUnif_holds PDicEx_holds RDicEx_holds UnifG_holds StabTriv_holds FixFwd_holds FixEq_holds FixGa_holds FixLoc_holds TanExists_holds FixFinite_holds PowSm_holds PwOver_holds SumPts_holds EigSame_holds

theorem FixZ_holds : FixZ := fixZ_of fixedPoints_int_base_holds LevelChange_holds

end UpperTheory.Gal.W2
