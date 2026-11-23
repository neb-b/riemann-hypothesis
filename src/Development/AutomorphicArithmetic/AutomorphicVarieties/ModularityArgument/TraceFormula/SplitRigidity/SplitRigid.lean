module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.ListOfMultiset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.AntiTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.PartCS

@[expose] public section

open UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.SR.splitRigid : UpperTheory.V.Z.Tf.SR.SplitRigid :=
  splitRigid_of (shareBd (logTwo extId) (crossUp extId)) (absShare (logTwo extId) (crossUp extId) partCS) antiTw
