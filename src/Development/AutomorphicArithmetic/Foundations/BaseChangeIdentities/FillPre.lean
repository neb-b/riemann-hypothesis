module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameBound
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.FrameRead
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.USideFree

@[expose] public section

theorem UpperTheory.BaseChangeIdentities.baseChangeN_of
    (hCF : PositivityTheory.Rg.BcB.F.FX.CandFin) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN := by
  have hFrameEx : PositivityTheory.Rg.BcB.F.FrameEx :=
    UpperTheory.HeckeLevelFrameExistence.frameEx_of_fin UpperTheory.BaseChangeIdentities.uSide hCF
  exact PositivityTheory.Rg.BcB.Plug2.bci_of hFrameEx
    UpperTheory.BaseChangeIdentities.FrameWordIdentity.frameBound
    UpperTheory.BaseChangeIdentities.GelfandReading.frameRead
