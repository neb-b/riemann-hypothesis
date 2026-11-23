module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048

@[expose] public section

namespace Formalism.L2.SG.Closed





open Formalism.L2.SG.Pf.NcReal.JX in
theorem CovolRef_outright : CovolRef :=
  covolRef_of_steps (coordCovol_of kapLaw_holds NOf.nofib_holds Formalism.L2.SG.Pf.NcReal.JX.CovB.blockCovol_holds)
    (refNBox_of Formalism.L2.SG.Pf.NcReal.JX.FR.frameRow_holds)


end Formalism.L2.SG.Closed
