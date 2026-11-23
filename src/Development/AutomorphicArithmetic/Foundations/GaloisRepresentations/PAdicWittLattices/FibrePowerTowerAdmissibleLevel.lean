module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNCong
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGSimOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOrbit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGenSm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0011

@[expose] public section

open UpperTheory.Gal.Int.Geo (KSEx KSNice)

universe u

namespace UpperTheory.Gal.G3

theorem nuInt_holds : NuInt := @pNuInt

theorem multBasic_holds : MultBasic := @pMultBasic @nuInt_holds

theorem kNBasic_holds : KNBasic := @pKNBasic

theorem sysOf_holds : SysOf := @pSysOf @nuInt_holds

theorem fibrePowerTower_admissibleLevel : AdmOf := @pAdmOf

theorem kNCong_holds : KNCong := @pKNCong

theorem gSimOf_holds : GSimOf := @pGSimOf @multBasic_holds

theorem relComp_holds : RelComp := @pRelComp

theorem tateDiff_holds : TateDiff := @pTateDiff

theorem tateTwist_holds : TateTwist := @pTateTwist @gSimOf_holds

theorem fullOf_holds : FullOf := @pFullOf

theorem relArith_holds : RelArith := @pRelArith

theorem transSelf_holds : TransSelf := @pTransSelf @multBasic_holds @relComp_holds @tateTwist_holds

theorem transComp_holds : TransComp := @pTransComp @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds

theorem homPull_holds : HomPull := @pHomPull

theorem tatePull_holds : TatePull := @pTatePull

theorem transPull_holds : TransPull := @pTransPull @homPull_holds @tatePull_holds

theorem transOfMap_holds : TransOfMap := @pTransOfMap @multBasic_holds @relComp_holds @tatePull_holds

theorem rigid_holds : Rigid := @pRigid

theorem isogFEt_holds : IsogFEt := @pIsogFEt

theorem transKer_holds : TransKer := @pTransKer @relComp_holds @tateDiff_holds @tateTwist_holds

theorem polUniq_holds : PolUniq := @pPolUniq

theorem mapOfIso_holds : MapOfIso := @pMapOfIso

theorem transDeep_holds : TransDeep := @pTransDeep @sysOf_holds @fibrePowerTower_admissibleLevel @fullOf_holds @relArith_holds

theorem transIso_holds : TransIso := @pTransIso @isoPts_holds @isogFEt_holds

theorem transOrbit_holds : TransOrbit := @pTransOrbit @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @kNCong_holds @transIso_holds

theorem transFree_holds : TransFree := @pTransFree @kNCong_holds

theorem genSm_holds : GenSm := @pGenSm

theorem powSm_holds : PowSm := @pPowSm @genSm_holds

theorem etDesc_holds : EtDesc := @pEtDesc @extPts_holds

theorem ptOrbit_holds : PtOrbit := @pPtOrbit @transComp_holds @transPull_holds @transOfMap_holds @transOrbit_holds @rigid_holds

theorem witComp_holds : WitComp := @pWitComp @transSelf_holds @transComp_holds @transPull_holds

theorem witCart_holds : WitCart := @pWitCart @transIso_holds

theorem witForget_holds : WitForget := @pWitForget @mapOfIso_holds @transSelf_holds

theorem witDeep_holds : WitDeep := @pWitDeep @kNBasic_holds @genSm_holds @transDeep_holds @witComp_holds @witForget_holds

theorem homDesc_holds : HomDesc := @pHomDesc @etDesc_holds

theorem polDesc_holds : PolDesc := @pPolDesc

theorem transDesc_holds : TransDesc := @pTransDesc @isogFEt_holds @tatePull_holds @homDesc_holds @polDesc_holds

theorem transCancel_holds : TransCancel := @pTransCancel @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @transIso_holds

theorem twFEt_holds : TwFEt := @pTwFEt @fEtBasic_holds @twGal_holds

theorem sigmaFEt_holds : SigmaFEt := @pSigmaFEt

theorem kSNice_holds : KSNice := @pKSNice @kNBasic_holds @powSm_holds @twFEt_holds @sigmaFEt_holds

theorem quotUniq_holds : QuotUniq := @pQuotUniq @etDesc_holds

theorem transUniqPt_holds : TransUniqPt := @pTransUniqPt @multBasic_holds @isogFEt_holds @transKer_holds @quotUniq_holds @polUniq_holds @mapOfIso_holds

theorem ptEq_holds : PtEq := @pPtEq @transSelf_holds @transComp_holds @transPull_holds @transUniqPt_holds @rigid_holds

theorem witUniq_holds : WitUniq := @pWitUniq @genSm_holds @extPts_holds @transSelf_holds @ptEq_holds

theorem descMap_holds : DescMap := @pDescMap @genSm_holds @etDesc_holds @ptEq_holds @ptOrbit_holds @witCart_holds

theorem witEx_holds : WitEx := @pWitEx @kNBasic_holds @genSm_holds @rigid_holds @witForget_holds @witDeep_holds @descMap_holds @transIso_holds @transCancel_holds @transDesc_holds

theorem witOne_holds : WitOne := @pWitOne @genSm_holds @witUniq_holds @witComp_holds @witForget_holds

theorem witTrans_holds : WitTrans := @pWitTrans @kNBasic_holds @ptEq_holds @ptOrbit_holds @witComp_holds

theorem witFree_holds : WitFree := @pWitFree @kNBasic_holds @transComp_holds @transPull_holds @transOfMap_holds @transFree_holds @ptEq_holds @witCart_holds @witEx_holds

theorem kSEx_holds : KSEx := @pKSEx @kNBasic_holds @witUniq_holds @witComp_holds @witCart_holds @witEx_holds @witOne_holds @witTrans_holds @witFree_holds

end UpperTheory.Gal.G3
