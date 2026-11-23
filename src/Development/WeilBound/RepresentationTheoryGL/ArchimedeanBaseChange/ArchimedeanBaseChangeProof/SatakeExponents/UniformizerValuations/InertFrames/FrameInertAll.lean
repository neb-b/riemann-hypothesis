module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.InertA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.AntiJMulSelf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.SatEx
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.SatUniqA

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Inert

theorem frameInert_all : InertPlaceEx ∧ WittEx ∧ UnifEx ∧ SatEx ∧ UnifOf ∧ SatUniq :=
  ⟨inertPlaceEx, wittEx, unifEx, satEx, unifOf, satUniq⟩

end PositivityTheory.Rg.BcB.F.Inert
