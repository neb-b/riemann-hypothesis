module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0015

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCnt0G
section
namespace Formalism.L2.SG.LocalCountModules.LocCnt0G

def LocCnt0G : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSide0 M r n true)

end Formalism.L2.SG.LocalCountModules.LocCnt0G
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCnt0L
section
namespace Formalism.L2.SG.LocalCountModules.LocCnt0L

def LocCnt0L : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSide0 M r n false)

end Formalism.L2.SG.LocalCountModules.LocCnt0L
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCntUG
section
namespace Formalism.L2.SG.LocalCountModules.LocCntUG

def LocCntUG : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSideU M r n true)

end Formalism.L2.SG.LocalCountModules.LocCntUG
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCntUL
section
namespace Formalism.L2.SG.LocalCountModules.LocCntUL

def LocCntUL : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSideU M r n false)

end Formalism.L2.SG.LocalCountModules.LocCntUL
end

