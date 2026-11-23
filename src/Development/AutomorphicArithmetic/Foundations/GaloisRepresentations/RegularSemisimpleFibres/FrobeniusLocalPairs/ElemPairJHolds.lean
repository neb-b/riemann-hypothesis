module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPair
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0009

@[expose] public section

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem elemPairJ_holds : UpperTheory.Gal.Join.ElemPairJ := elemPairJ elemPair

theorem finTrace_holds (h : GlobalTheory.DZA.InflMatching) (h₁ : G.VarEx) (h₂ : G.VarTrace) (h₃ : G.NormInt) : FinTrace :=
  finTrace resEx finAct inflFacts frobFacts (inflTrace h h₁ h₂ h₃)

end UpperTheory.Gal.InertialTypesAlt.L
