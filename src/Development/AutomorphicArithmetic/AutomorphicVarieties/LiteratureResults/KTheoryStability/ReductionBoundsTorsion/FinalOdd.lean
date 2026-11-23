module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SurjectivityCase.SSurjOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.SWtOddOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddSpanRank.SBStarOddOf

@[expose] public section

namespace PositivityTheory.KB

theorem bStarOdd : BStarOdd :=
  sBStarOdd_of sChain sSep' sBridge sStab
    (sSurj_of sPrime_of sHecke sHt_of sPU sMom sWhit sCen sGap_of sLoc sMean_of sInv)
    (sWtOdd_of sChain sEv sPsi sStokes_of)

end PositivityTheory.KB
