module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.GelfandValueOne.CasVal
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.EmbeddingConjugation.CoordConjEmbedding
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.FrameExistence.FrameHolds
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryTwistCoordinates.UnitTw
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.DeterminantDerivative.BigRep
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.MatrixConjugateSums.Summand
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410

@[expose] public section

namespace PositivityTheory.Rg.Cz

theorem clozelCohomological_of_rest (h1 : KType) (hgk : GKData) (hw : WhitLie) (hka : KugaAbs) (hkg : KugaGlue)
    (hcg : CoefGlue) (hco : Cochain) (hcb : CasBound) : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of h1 J.kData_holds hgk hw GlobalTheory.CompanionTheory.RgCz.charInt J.unitTw_holds
    (hcg hcb J.bigRep_holds J.bigCx_holds J.summand_holds hco J.casVal_holds)
    (hkg hka J.frame_holds GlobalTheory.CompanionTheory.FrameCasimir.frameCas J.cxExpand_holds J.tensForm_holds GlobalTheory.CompanionTheory.GKHarmonic.harmonic)

end PositivityTheory.Rg.Cz
