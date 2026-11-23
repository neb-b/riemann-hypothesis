module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlagOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.LOfOfKChain
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataModel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommute
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagFieldHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffMulRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopy
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceMulConjTranspose

@[expose] public section

namespace PositivityTheory.RgBcC

theorem lef_top (hE : WaveEx) (hS : WaveSpeed) (hK : KerEx) (hM : MultAlg) (hC : LfSt.KChain) : Lef := by
  have hKer : VC.VCKer := VC.vcKer_of
    (VC.kerComm_of GlobalTheory.CompanionTheory.WaveInv.waveN GlobalTheory.CompanionTheory.WaveField.waveA)
    (VC.kerNId_of GlobalTheory.CompanionTheory.LgBound.lgCpt GlobalTheory.CompanionTheory.ParamInt.intSmooth)
    (VC.nAvg_of GlobalTheory.CompanionTheory.ParamInt.intSmooth GlobalTheory.CompanionTheory.LgBound.lgCpt GlobalTheory.CompanionTheory.NilUnimod.nilUni)
    VC.trZero GlobalTheory.CompanionTheory.LgBound.lgCpt
  have hV : VCSt := VC.vcOf_of GlobalTheory.CompanionTheory.ParamInt.intSmooth hKer hE hS hM GlobalTheory.CompanionTheory.GelC.gelComm
    GlobalTheory.CompanionTheory.GelFlagPf.gelFlag_holds GlobalTheory.CompanionTheory.FlagHerm.flagField_holds GlobalTheory.CompanionTheory.NilUnimod.nilUni
    GlobalTheory.CompanionTheory.KerZeroPf.main
  have hCh : Chain := LfSt.chainOf'_holds hE hS GlobalTheory.CompanionTheory.GelC.gelComm GlobalTheory.CompanionTheory.KerZeroPf.main
  have hL : LSt := LfSt.lOf_of_kChain hC hE hS hK hM hCh _root_.GlobalTheory.CompanionTheory.ConeHaar.coneSt _root_.GlobalTheory.CompanionTheory.SuperHomot.homot
    GlobalTheory.CompanionTheory.SuppBound.suppSt
  exact lef_of cxEx_model hV hL

end PositivityTheory.RgBcC
