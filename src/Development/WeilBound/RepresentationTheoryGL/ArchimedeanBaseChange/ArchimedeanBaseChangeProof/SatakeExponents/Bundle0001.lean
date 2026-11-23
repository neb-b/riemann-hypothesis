module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.RunFinChain
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GelfandValueContinuity.ReadLimitOfEfinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameEx0Plug
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LPermSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PLevelFactorB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PFinFamOf
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscreteSpectrum

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.BciOf
section
noncomputable section

namespace PositivityTheory.Rg.BcB.Plug2

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.F5

theorem bci_of (h1 : FrameEx) (h3 : FrameBound)
    (h4 : FrameRead) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  PositivityTheory.Rg.BcB.F.Rig.fieldN_of_run
    (runFin_chain (finFamOf_holds levelFactor _root_.GlobalTheory.CompanionTheory.FinDiscN.finDiscN) PositivityTheory.Rg.BcB.F.Rig.weightEx PositivityTheory.Rg.BcB.F.Rig.permSat
      _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg (genEx_of (PositivityTheory.Rg.BcB.F.Rd.P.readLimit_of_efinal PositivityTheory.Rg.BcB.SpectralAccumulation.eFinal_holds) _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg PositivityTheory.Rg.BcB.F.Ex0.frameEx0 h1 frameOk₀ h3 h4))

end PositivityTheory.Rg.BcB.Plug2
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.BciOfAlt
section
noncomputable section

namespace PositivityTheory.Rg.BcB.Plug2B

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.F5

theorem bci_of (h1 : FrameEx) (h3 : FrameBound)
    (h4 : FrameRead) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  PositivityTheory.Rg.BcB.F.Rig.fieldN_of_run
    (runFin_chain (finFamOf_holds levelFactor _root_.GlobalTheory.CompanionTheory.FinDiscN.finDiscN) PositivityTheory.Rg.BcB.F.Rig.weightEx PositivityTheory.Rg.BcB.F.Rig.permSat
      _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg (genEx_of (PositivityTheory.Rg.BcB.F.Rd.P.readLimit_of_efinal PositivityTheory.Rg.BcB.SpectralAccumulation.eFinal_holds') _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg PositivityTheory.Rg.BcB.F.Ex0.frameEx0 h1 frameOk₀ h3 h4))

end PositivityTheory.Rg.BcB.Plug2B
end
end

