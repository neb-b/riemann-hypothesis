module

public import Formalism.LocalToGlobal.ThetaChr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.LocalToGlobal.HermitianForms.Bundle0008
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.LatticeGeometry.Inhabited
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure LinkedFamilyData (ex : Extra D L hT Gi Gl K Y cX) where
  host : Host.HostTied D
  level : Host.LevelTied D

  cols : Forms.ColsTiedSym D

  full : Forms.ColsFullS cols

  extra : Forms.ColsExtraTiedS full ex
  provA : TH.ProvA
  theta : Theta.AllTied D ex.th provA
  twIn : TwIn D
  n : NormalizedTwistCompatibility D ex.nch twIn
  frameN : Host.SameFrameN host n.gal.fr.jE
  thetaChr : Host.ThetaChrTied D n.cf ex.nch n.tp ex.th
  chrVal : Host.ValLL0 D n.cf
  chrDt : Host.DtTied D n.cf
  chrN : Host.NCharTied D n.cf ex.nch n.tp
  chrGal : Host.NGalChrTied D n.cf ex.nch n.tp
  chrPsi : Host.PsiChoiceCompatible D n.cf ex.nch n.tp
  sameChr : JoinChr.SameChr theta.T thetaChr
  what₂ : Rows.RowsCompatible D host n.cf n.tp

  inK : Y.Lev → ℕ → Prop

  geo : Geo.GeoTiedP Y inK

  tw : Forms.SymmetricTwistedColumnsAtPrimes n.tp cols ex.tw

  emt : Rows.EMtTied D cols tw

  g : G.GroupCompatibilityAll D hT ex.cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (cols.forms u).to0

end

end Formalism.L2
