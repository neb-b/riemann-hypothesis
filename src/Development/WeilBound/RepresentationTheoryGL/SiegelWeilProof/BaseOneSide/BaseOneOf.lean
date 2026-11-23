module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneBase.MassOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.PlugInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0686
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityOfMassOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0688
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0715
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693

@[expose] public section

namespace PositivityTheory.Rg.Base1

theorem baseOne_of (hM : PositivityTheory.SiegelWeilFormula.Densx.MassOne) : PositivityTheory.SiegelWeilFormula.Densx.BaseOne :=
  GlobalTheory.T.siegel_weil_rank_one_base_case (_root_.GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one hM) (_root_.GlobalTheory.CompanionTheory.SW.BaseSimil.simil _root_.GlobalTheory.CompanionTheory.RgBase.ScalFib.scal) _root_.GlobalTheory.CompanionTheory.SW.BaseHasse.hasse
    (_root_.GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of _root_.GlobalTheory.CompanionTheory.TateRes.tate (_root_.GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi _root_.GlobalTheory.CompanionTheory.Equi.equi) _root_.GlobalTheory.CompanionTheory.RatioBase.ratio _root_.GlobalTheory.CompanionTheory.RgBase.hEx _root_.GlobalTheory.CompanionTheory.SW.BaseTest.testEx _root_.GlobalTheory.CompanionTheory.SW.RankOne.dens
      (_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside _root_.GlobalTheory.CompanionTheory.Equi.equi) (_root_.GlobalTheory.CompanionTheory.RgBase.Theta.thetaId _root_.GlobalTheory.CompanionTheory.RgBase.ScalFib.scal (_root_.GlobalTheory.CompanionTheory.RankOneLoc.locR _root_.GlobalTheory.CompanionTheory.RgBase.ScalFib.scal hM)))

theorem baseOne : PositivityTheory.SiegelWeilFormula.Densx.BaseOne := baseOne_of PositivityTheory.SiegelWeilFormula.BaseOne.massOne

theorem densEq : PositivityTheory.SiegelWeilFormula.Gen.DensEq := PositivityTheory.SiegelWeilFormula.Densx.densEq_of_one baseOne PositivityTheory.SiegelWeilFormula.BaseOne.massOne

end PositivityTheory.Rg.Base1
