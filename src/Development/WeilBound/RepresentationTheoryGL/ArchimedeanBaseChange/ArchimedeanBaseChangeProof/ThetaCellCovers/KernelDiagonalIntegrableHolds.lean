module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.MahlerFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.CutCountOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0332
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330

@[expose] public section

namespace PositivityTheory.Rg.BcB.E1

open D1

theorem sizeCont : SizeCont := GlobalTheory.CompanionTheory.SizeCont.sizeCont szFin
theorem degRight : DegRight := GlobalTheory.CompanionTheory.DegRightProof.degRight_of mulF mulI szFin finSupp
theorem redBasic : RedBasic := redBasic_of ratProper_holds sizeCont
theorem cutBox : CutBox := cutBox_of' degBasis degAdelic degBdd
theorem redCell : RedCell := redCell_of sizeBasic degBdd degRat degRight torNorm_holds cutBox redBasic
theorem cutRed : CutRed := cutRed_of degRat cellCover_holds cutBox redBasic redCell
theorem cntPair : CntPair := cntPair_of ratProper_holds thetaBasic_holds
theorem wtCount : WtCount := wtCount_of ratProper_holds cellSum cellCover_holds redBasic redCell GlobalTheory.CompanionTheory.LatticeSum.latSum
theorem cutCount : CutCount := cutCount_of redBasic cutRed wtCount
theorem vecsEx : VecsEx := GlobalTheory.CompanionTheory.DualVectorFamily.vecsEx_of ratProper_holds kerBasic kerLin cntBasic cntPair vecEx vecNorm vecInner ptEq
theorem lBound : LBound := GlobalTheory.CompanionTheory.LBoundProof.lBound_of mahler_holds cutCount
theorem sFun_holds : SFun := sFun_of vecsEx lBound
theorem sBound_holds : F.SBound := sBound_of (sb_of sFun_holds)
theorem bridge_holds : F.Bridge := bridge_of (GlobalTheory.CompanionTheory.PairDom.prodDom ratProper_holds)
theorem opEx_holds : F.OpEx := opEx_of ratProper_holds opExA opAdj opMul
theorem kernel_operator_exists_holds : E.SmoothSeminormGrowth := kernel_operator_exists_of opEx_holds
theorem growthJ_of_ell (h : D4.EllFormula2J) : GrowthJ := growthJ_of h sBound_holds bridge_holds domEx_holds


end PositivityTheory.Rg.BcB.E1
