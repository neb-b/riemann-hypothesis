module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SwtAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.Bundle0001

@[expose] public section

namespace PositivityTheory.KB

open BlockInvariants BlockEvaluationBounds in
theorem sWtOdd_of : SChain → SEv → SPsi → SStokes → SWtOdd := fun _ hE _ hS =>
  swtOdd hE hS (fft_of cplx sw1 sw2) aGood wPad weylTwoBlockMatrix wInv wCyc tStab tBlk pStab blockSum_preserves_cone wOneOdd wRot

end PositivityTheory.KB
