module

public import Formalism.SubspaceCounting.Bundle0001
public import Formalism.SubspaceCounting.SubspaceCountingProofs.Bundle0001
public import Formalism.SubspaceCounting.SubspaceCountingProofs.Bundle0002
public import Formalism.SubspaceCounting.SubspaceCountingProofs.WalkSharp
public import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbitsRefined
public import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
public import Mathlib

@[expose] public section

namespace Formalism.G0.Top

theorem walkSharp : Formalism.G0.WalkSharp := Formalism.G0.walkSharp_true

theorem subspaceCount : Formalism.G0.SubspaceCount := Formalism.G0.countSubspacesEq

theorem typeIIDown : Formalism.G0.TypeIIDown := Formalism.G0.countAboveRangeCodimFormula

theorem markedRun : Formalism.G0.MarkedRun := Formalism.G0.marked_run

end Formalism.G0.Top
