module

public import Formalism.LocalToGlobal.ClassS
public import Formalism.LocalToGlobal.ClassSK
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
public import Formalism.LocalToGlobal.RatioJoints.CharacterProductEqOne
public import Formalism.LocalToGlobal.UnitaryNorms.DatumS
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure RecT (ex : Extra D L hT Gi Gl K Y cX) where

  T : TiedDataSK ex

  pin : Rows.RowPinMin T

  joints : JointsS T.toTiedDataS

  host : HostDatumS T.toTiedDataS

  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W

end

end Formalism.L2
