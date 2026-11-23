module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftInv

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PEvValChain

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc Formalism.MainNotions.G.CmpJ.PCmpLiftTw Formalism.MainNotions.G.CmpJ.PCmpLiftInv

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem evValLe_of_wt (S : StepIn M i hi G) (β : S.Ch) (hw : WtTie (Hc S β).P (S.loc β).rk S.pos (M.lam i)) :
    EvValLe S β := by
  intro Q hQ
  exact Formalism.L2.G.EvLe.evC_le (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
    (atInfGL (embT D) (S.loc β).B⁻¹) (M.lam i) hw Q hQ

theorem cmpLiftOf_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : CmpLiftOf S e := by
  intro hS H X
  exact cmpLiftOf_of_evVal S e (fun β => evValLe_of_wt S β (H β).wt) hS H X

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PEvValChain
