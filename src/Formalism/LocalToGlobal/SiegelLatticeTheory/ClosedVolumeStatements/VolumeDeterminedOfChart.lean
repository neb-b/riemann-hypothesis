module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlkOfOfPtEntry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerLatticeCoordinatesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0092

@[expose] public section

namespace Formalism.L2.SG.Closed

theorem volume_determined : Formalism.L2.SG.VolPin.VolumeOddGeneric :=
  Formalism.L2.SG.Pf.VolPinAsm.volume_generic_odd_of_rep Formalism.L2.SG.Pf.VolPinAsm.dictC_holds Formalism.L2.SG.NGCut.StabilizerCovolume.covolOne3C_holds

end Formalism.L2.SG.Closed
