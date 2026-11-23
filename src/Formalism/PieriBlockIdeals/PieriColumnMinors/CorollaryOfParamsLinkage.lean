module

public import Formalism.PieriBlockIdeals.StatementDown
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
public import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle0008
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RealOfSkeleton
public import Formalism.PieriBlockIdeals.PieriColumnMinors.IrreducibleGeneration

@[expose] public section

namespace Formalism.CohomologicalDescent.Down

theorem hG : LD.LemmaDGraded :=
  LR.real_of_pieri LPR.pieri_real_form (ColumnMinorsFromPieri.columns_real_of_pieri_real LPR.pieri_real_form)

theorem inclusion_w_real_holds : InclWReal := ShortWeightBounds.inclusion_w_real_holds hG

end Formalism.CohomologicalDescent.Down
