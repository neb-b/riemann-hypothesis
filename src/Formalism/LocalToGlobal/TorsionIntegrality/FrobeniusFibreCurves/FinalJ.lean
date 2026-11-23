module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalI
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FibreIntegerInstanceHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormXLeOneOfNotInKernel
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Th0TwoAnalyticOf

@[expose] public section

namespace Formalism.L2.Th1.B

theorem halfFibreExists : HalfFibreExists := Half.half_fibre_exists_holds
theorem fibreZInstance : FibreZInstance := Fib.fibre_integer_instance_holds
theorem halfShiftSeries : HalfShiftSeries := Fib.half_shift_series_holds
theorem fibreMap : FibreMap := Half.fibre_map_holds
theorem th0TwoAnalytic : ThetaZeroTwoAnalytic :=
  An2.Th0TwoAnalytic_of halfFibreExists fibreZInstance halfShiftSeries fibreMap

end Formalism.L2.Th1.B
