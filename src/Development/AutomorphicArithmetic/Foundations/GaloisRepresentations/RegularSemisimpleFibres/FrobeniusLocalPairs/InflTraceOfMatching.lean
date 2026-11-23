module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarTraceHolds

@[expose] public section

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem finTrace_of_matching (h : GlobalTheory.DZA.InflMatching) : FinTrace :=
  finTrace_holds h G.varEx_holds G.varTrace_holds G.normInt_holds

end UpperTheory.Gal.InertialTypesAlt.L
