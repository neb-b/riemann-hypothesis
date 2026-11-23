module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0072
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftingOfCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0081
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
theorem sp4In0_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') :
    _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.sp4In_alt (adjoint_lift_of_prints hH).coh
    _root_.UpperTheory.V.FW.ferreroWashington
    (_root_.UpperTheory.V.Z.Bc.seedIIs_alt hH)
    (_root_.UpperTheory.V.Z.Win.Birth.fourth_initial_of_prints_h hH)
    (pmEx_of_printsH hH)
end UpperTheory.V.HV.DescentVanishingReductions
end
