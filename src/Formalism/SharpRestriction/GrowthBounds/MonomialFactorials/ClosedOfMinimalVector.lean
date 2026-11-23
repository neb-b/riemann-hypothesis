module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfSplittingMatrix
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0018

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_minimal_vector (D : Formalism.BasicNotions.D7) (hO : OrthMin) (hM : GoodLeSmallMat) (h : RestWinE D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_splitting_matrix D (orthSplit_of_min hO) hM h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
