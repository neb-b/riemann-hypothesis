module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.Models
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.IntertwinerAdjoints.Imports
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionExistenceHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.Imports
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.StepM
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.FarClosed

@[expose] public section

namespace PositivityTheory.RgHe

theorem occ : Occ :=
  Dec.walk (Sl.stepL LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (SM.stepM LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (PositivityTheory.RgHe3.base LowestKTypeModel.models FrameF.frame)

end PositivityTheory.RgHe
