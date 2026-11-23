module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.TwSwap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.IsIntIffV

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Th in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.stUnit : UpperTheory.V.Z.Tf.GlobalTraceComparison.StUnit :=
  stUnit_of (twSwap orbFub) twLin cvRing (cvComm2 cvGelfand) theta_involution_facts genTw
