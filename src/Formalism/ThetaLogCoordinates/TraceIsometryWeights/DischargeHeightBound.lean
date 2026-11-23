module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.FinalP
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Bundle0003
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Bundle0004

@[expose] public section

namespace Formalism.InvariantFactorPaths.PW.Top

theorem weylInt : WeylInt := weyl_integral_holds
theorem weylP : WeylP := weylP_of weylInt lattice_basis_polynomial

private theorem intP_statement : IntP := by
  have hInv : InvInv := invariant_inverse_holds
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial

theorem extP : ExtP := extP_of intP_statement
theorem dischargeW : DischargeW := dischargeW_of weylP
theorem dischargeE : DischargeE := dischargeE_of extP

end Formalism.InvariantFactorPaths.PW.Top
