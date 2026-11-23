module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.BlockCandOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.FrameMatrixPowerHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreePrecursors.PreOfTreeHolds

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.BC

theorem level_reading_holds : FG.LevRead := FG.levReadOf_holds (levIdem slots)

theorem block_candidates_of_inputs (h1 : ChiTr) (h2 : LimAt) (h3 : Ident) : BlockCand :=
  blockCand_of h1 h2 h3 (powNeOf_holds FA.convMul_holds) SpectralAccumulation.preOfTree_holds RS.joinEx_holds level_reading_holds
    (FG.frGood_of level_reading_holds) FG.frame_weight_holds

end PositivityTheory.Rg.BcB.F.BC
