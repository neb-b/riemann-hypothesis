module

public import Mathlib
public import Formalism.MeanHeightDescent.MuMaxMinkowski
public import Formalism.MeanHeightDescent.BadRowsNumeric
public import Formalism.MeanHeightDescent.CombinedAverageDegreeBound
public import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle0001
public import Formalism.MeanHeightDescent.AverageDegreeBounds.SumComponents

@[expose] public section

open Finset Module NumberField

namespace Formalism.ExtensionFiltration

theorem mean_height_sum_bound_holds : CombinedAverageDegreeBound := combinedAverageDegreeBound_of meanHeightLowerBound sumComponents'

end Formalism.ExtensionFiltration
