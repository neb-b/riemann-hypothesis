module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bridge
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SecOneConst

@[expose] public section

namespace PositivityTheory.Rg.Sw.SP

theorem sPrime_of_minor (h : MinorFormula) : SPrime :=
  sPrime_of bridge (cayDiv_of comm (minorZ_of h) (minorZ'_of h) null)

theorem wrOrd_of_minor (h : MinorFormula) : PositivityTheory.SiegelWeilFormula.Gen.WROrd := wrOrd_of (sPrime_of_minor h)

end PositivityTheory.Rg.Sw.SP
