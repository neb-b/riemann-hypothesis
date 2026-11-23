module

public import Formalism.GrowthSums.FactorialBaseGrowth.Bundle0001
public import Formalism.GrowthSums.FactorialBaseGrowth.Bundle0002
public import Mathlib

@[expose] public section

namespace Formalism.GrowthSums.Top

theorem segmentBound : Formalism.GrowthSums.SegmentBound := Formalism.GrowthSums.segment_bound_holds
theorem nextEvenTop : Formalism.GrowthSums.NextEvenTop := Formalism.GrowthSums.next_even_top_holds
theorem topCount : Formalism.GrowthSums.TopCount := Formalism.GrowthSums.top_count_holds

end Formalism.GrowthSums.Top
