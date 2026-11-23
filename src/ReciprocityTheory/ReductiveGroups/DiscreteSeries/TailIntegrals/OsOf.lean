module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OscillatoryBound

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem sub : SUB := quadraticSublevelDecay'

theorem ker : KER := planarKernelBound'

theorem slow : SLOW := slowWeightBound'

end ReciprocityTheory.ChartRestriction.DS.Xi
