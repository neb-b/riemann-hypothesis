module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovLink
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ExistsIsoOfCart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ActGActGInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsDominantGenericFibre
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OStepF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftSys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PNormExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0005

@[expose] public section

namespace UpperTheory.Gal.FiniteEtaleModels

open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.CovMain UpperTheory.Gal.crystallineComparison.Mod

theorem stepA : StepA := stepA_holds (multUnit_of mIn) (latGen_of mIn) (clsEx_of mIn) (trEta_of mIn) (trBack_of mIn) (qComp_of mIn)

theorem baseFet : BaseFet := baseFet_holds (powCart_of mIn) (piFet_of mIn)

theorem stepB : StepB :=
  stepB_of (tjExG_of esNorm_link esGen_link objTri_holds pullIsog_holds pullKer_holds)
    (bRead_of (isogG_of (trEta_of mIn) (trBack_of mIn) (multUnit_of mIn) (trTj_of mIn)) (qObj_of mIn) (qComp_of mIn) objTri_holds)
    (bKer_of (secInjG_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds) (trEtaPt_of mIn))
    (bLev_of latB_holds etaPtB_holds etInj_holds) (descExt_of normExt_holds) baseFet O.baseOnto pulledEx_holds

theorem quotOf : QuotOf := quotOf_holds (powCart_of mIn) (piInv_of mIn) (piFet_of mIn) (piSep_of mIn) (congCRT_of mIn) O.baseOnto

theorem extEx : ExtEx := extEx_holds mIn (powProj_of mIn)

theorem ksGood_holds : KSGood :=
  ksGood_of (siteEx_of mIn) (numEx_of mIn) (clsEx_of mIn) ksCover_holds (piInv_of mIn) (powCart_of mIn) extEx quotOf stepA stepB O.stepF
    degGen_holds fEtExt_holds liesAbs_holds

end UpperTheory.Gal.FiniteEtaleModels
