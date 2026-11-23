module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle0005

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

theorem stepPairG_holds : StepPairG := stepPairG_of_fwd_bwd fwdEx bwdEx

theorem algAll_holds : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := algAll_of stepPairG_holds

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
