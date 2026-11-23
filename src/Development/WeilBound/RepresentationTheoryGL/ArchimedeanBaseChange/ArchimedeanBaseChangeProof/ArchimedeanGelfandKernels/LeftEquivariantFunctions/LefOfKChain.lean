module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.LefTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal

@[expose] public section

namespace PositivityTheory.RgBcC

theorem lef_of_kChain (hC : LfSt.KChain) : Lef :=
  lef_top wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.2.2.1 wave_existence_speed_multiplicity.2.2.2 hC

end PositivityTheory.RgBcC
