module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

@[expose] public section

namespace Formalism.L2.SG.Pf

theorem massAC_holds : Formalism.L2.SG.NormCut.MassAC :=
  massAC_of Formalism.L2.SG.Closed.NeatC_holds

end Formalism.L2.SG.Pf
