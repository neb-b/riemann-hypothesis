module

public import Mathlib
public import Formalism.MeanHeightDescent.MuMaxMinkowski
public import Formalism.MeanHeightDescent.BadRowsNumeric
public import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle0001
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeFullAssemblyHolds
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
public import Formalism.MeanHeightDescent.AverageDegreeBounds.CombinedAverageDegreeBoundOf
public import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
public import Formalism.MeanHeightDescent.AverageDegreeBounds.SumComponents
public import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower

@[expose] public section

namespace Formalism.ExtensionFiltration

theorem lcvMu : LcvMu := log_covolume_slope_mu
theorem descentSlope : DescentSlope := descent_slope
theorem spanMuMin : SpanMuMin := span_min_slope
theorem goodBadCut : GoodBadCut := good_bad_split
theorem twistLower : TwistLower := twist_lower_bound
theorem muMaxMinkowski : MuMaxMinkowski := max_slope_minkowski
theorem mean_height_sum_bound : CombinedAverageDegreeBound := mean_height_sum_bound_holds

end Formalism.ExtensionFiltration
