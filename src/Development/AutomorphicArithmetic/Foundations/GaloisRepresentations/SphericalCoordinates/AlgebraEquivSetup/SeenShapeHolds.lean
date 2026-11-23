module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ValLeOneOfForall

@[expose] public section

namespace UpperTheory.Gal.W2.Seed

open UpperTheory.Gal.Int.Geo.Pl (dict_holds sides_holds levBasic_holds)
open UpperTheory.Gal.CertificateRingHomMap (pLocComm_of pThLoc_of)

theorem tfCen_holds : TfCen := pTfCen pAvgK pTfAdm
theorem tfAct_holds : TfAct := pTfAct pAvgK pDosetCosets pTfAdm
theorem tfIdem_holds : TfIdem := pTfIdem pTfAdm tfCen_holds
theorem tfMulL_holds : TfMulL := pTfMulL pTfAdm tfAct_holds pDosetIff
theorem tfMulR_holds : TfMulR := pTfMulR pAvgK pTfAdm pDosetIff
theorem tfLoc_holds : TfLoc := pTfLoc pTfAdm tfAct_holds pDosetIff
theorem knIff_holds : KNIff := pKNIff latCoord_holds
theorem atApart_holds : AtApart := pAtApart pJEq
theorem levFact_holds : LevFact := pLevFact atApart_holds pIntConj
theorem knIdx_holds : KNIdx := pKNIdx (pKNOpen knIff_holds)
theorem pPart_holds : PPart := pPPart pJEq
theorem memAct_holds : MemAct := pMemAct pMemSum pSumDoset tfAct_holds pDosetCosets
theorem memDeck_holds : MemDeck := pMemDeck pMemSum tfCen_holds
theorem levSec_holds : LevSec := pLevSec pIntConj
theorem knFact_holds : KNFact :=
  pKNFact knIff_holds pFacEq atApart_holds pCongGrpEx (pCongConj pLocComm_of) pLocComm pLocComm_of
theorem siteFact_holds : SiteFact := pSiteFact dict_holds sides_holds pIntConj pLocComm_of
theorem stabKer_holds : StabKer := pStabKer pFacEq knFact_holds pCongGrpEx
theorem seenShape_holds : SeenShape := pSeenShape stabKer_holds siteFact_holds (pCenFacts sides_holds) levBasic_holds pLocComm_of
theorem seenActs_holds : SeenActs := pSeenActs pMemSum memAct_holds memDeck_holds seenShape_holds levBasic_holds knIdx_holds
theorem actsConv_holds : ActsConv := pActsConv pTfAdm tfIdem_holds
theorem phiTy_holds : PhiTy := pPhiTy pPart_holds levSec_holds pFacEq pLocComm

theorem tyFact_holds : Spc.TyFact :=
  pTyFact pFacEq levSec_holds levFact_holds atApart_holds pCongGrpEx pDenom pLocComm pLocComm_of
theorem memFn_holds : Spc.MemFn := pMemFn seenShape_holds seenActs_holds actsConv_holds tyFact_holds
theorem phiEx_holds : Spc.PhiEx :=
  pPhiEx phiTy_holds seenShape_holds seenActs_holds tyFact_holds tfAct_holds tfCen_holds (tEig_of_thLoc (pThLoc_of pLocComm_of CertificateRingHomMap.pOfUBij_of)) atApart_holds pFacEq pJEq
    pLocComm

end UpperTheory.Gal.W2.Seed
