module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.PreEquivSymm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.Bundle0002

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.FX

theorem candFin_of_jEigFin (hJ : PositivityTheory.Rg.BcB.F.Tail.JEigFin) : CandFin :=
  Bo.candFin_of hJ Bo.Tw.FinStrict_holds Bo.StrictEqv_holds Bo.StrictPre_holds
    Bo.StrictProd_holds Bo.StrictJoin_holds Bo.CandParts_holds Bo.LevOpen_holds Bo.IsoInv_holds Bo.AdmProd_holds

end PositivityTheory.Rg.BcB.F.FX
