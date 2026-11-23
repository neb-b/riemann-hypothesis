module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SwtAll

@[expose] public section

namespace PositivityTheory.KB

theorem sInv_of : SChain → SEv → SPsi → SStokes → SInv := fun hC hE hP hS =>
  BlockInvariants.sinv_of_swt hC hP hS BlockInvariants.aGood (BlockInvariants.swt_all hE hS)

end PositivityTheory.KB
