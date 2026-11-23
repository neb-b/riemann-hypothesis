module

public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramHook
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramTopExact
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TwistedLatticeNaturality
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002

@[expose] public section

namespace Formalism.DivisionValues

theorem latticeGlue : LatticeGlue := lattice_gluing

theorem height_constant_bound : HeightBoundConstant := height_constant_first

theorem rowsHook : RowsHook := young_diagram_hook

theorem rowsStepEOrigin : RowsStepEOrigin := young_diagram_step_origin

theorem shiftMu : ShiftMu := by
  unfold ShiftMu
  exact shift_slope_mu

theorem shiftEx : ShiftEx := by
  unfold ShiftEx
  exact shift_existence

theorem divIntoDualShift : DivIntoDualShift := divisor_into_dual_shift

theorem primeLogSum : PrimeLogSum := prime_log_sum_bound

end Formalism.DivisionValues
