module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmD
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0012

@[expose] public section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

theorem fgSl_holds : FgSl := fun _ _ _ _ _ _ _ _ _ hU hT hfg =>
  ⟨BlockFiniteGeneration.LS_fg hU hT hfg (BlockSlices.expand hU hT), BlockFiniteGeneration.RS_fg hU hT hfg (BlockSlices.expand hU hT)⟩

theorem blocks_holds : Blocks := blocks_of fgSl_holds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
