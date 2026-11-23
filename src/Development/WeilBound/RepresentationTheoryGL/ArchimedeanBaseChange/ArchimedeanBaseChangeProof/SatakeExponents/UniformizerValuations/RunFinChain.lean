module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DiagCommOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PeakTraceBoundHolds

@[expose] public section

namespace PositivityTheory.Rg.BcB.F

theorem runFin_chain (hF : F5.FinFam) (hW : WeightEx) (hQ : PermSat) (hD : Eig.DiagAlg) (hG : GenEx) : One.RunFin :=
  F5.runFin_of (runT_of peak_trace_bound_holds (setupEx_of setupAlg (dataEx_of (diagComm_of hD) genToData hG))) hF hW hQ

end PositivityTheory.Rg.BcB.F
