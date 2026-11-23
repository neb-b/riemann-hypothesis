module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameBound
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.USideFree
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FinalAllB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PJEigB
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FillPre
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameEx

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.BaseChangeNB
section
namespace UpperTheory.BaseChangeIdentities

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F in
theorem baseChangeNB : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  Plug2B.bci_of
    (HeckeLevelFrameExistence.frameEx_of_fin uSide (FX.candFin_of_jEigFin Tail.JB.jEigFin))
    FrameWordIdentity.frameBound FinalAllB.frameRead_holdsB

end UpperTheory.BaseChangeIdentities
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.DefiniteNHolds
section
theorem UpperTheory.BaseChangeIdentities.baseChangeN : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  UpperTheory.BaseChangeIdentities.baseChangeN_of UpperTheory.HeckeLevelFrameExistence.candFin
end

