module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

@[expose] public section

open Formalism.L2.SG.GGMirabolic

namespace GlobalTheory.CompanionTheory.GG

theorem gelfandGraevMultOne_holds : GelfandGraevMultOne :=
  Formalism.L2.SG.Closed.GelfandGraevMultOne_holds

end GlobalTheory.CompanionTheory.GG
