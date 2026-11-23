module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS

@[expose] public section

namespace Formalism.MainNotions.BesselDiscreteSeries

theorem lowest_K_type_mult_one_of_gaps : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG := by
  intro N ε lam H _ _ σ hp hσ h hg hthr
  have : CompleteSpace H := hσ.1
  exact (ReciprocityTheory.ChartRestriction.DS.isDS_props_of_gap N ε lam hp h hg hthr H σ hσ).2.1

end Formalism.MainNotions.BesselDiscreteSeries
