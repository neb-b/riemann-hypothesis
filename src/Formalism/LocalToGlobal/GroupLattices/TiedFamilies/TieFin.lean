module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieAll
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.L2.G.Cmp Formalism.L2.Herm

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (H : FullTiedNoG D)
  (I0 : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (H.base.lev0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB D B)

def idStd : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (H.base.lev0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  fun u w hg => locIdStd D u w hg (I0 u w hg) B hBs
    (Classical.choose (companion_of_baseTied D H.base.toHermCols H.atT H.baseL u))
    (Classical.choose_spec (companion_of_baseTied D H.base.toHermCols H.atT H.baseL u))

variable (sc : Scale) (Ce : ℝ) (T : ∀ u : D.what₂.Word, Forms0 D u)
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (H.base.lev0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

variable {D H I0 B hBs sc Ce T ψ hd}

end Formalism.L2.G
