module

public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalisedAdaptedVectorZero
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def NormalClausesG (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D))
    (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (NormalFrames (betaYOf βY) e ev z κ s Pg Pg ∧ NormalFrame0 (betaYOf βY 0) Pg Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg



end Formalism.IndefR.Seed.Frm

end
