module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0096

@[expose] public section

namespace Formalism.L2.SG.Closed

theorem CutLeavesDeep_outright (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.Pf.Coef.CutLeavesDeep D := Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.cutLeavesDeep_of_betaInt D
  (fun _ _ _ u u' F0 what₂ => Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.betaInt_holds _ u u' F0 what₂)

end Formalism.L2.SG.Closed
