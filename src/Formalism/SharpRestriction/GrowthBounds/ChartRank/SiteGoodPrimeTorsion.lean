module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVinRec
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypInvLe
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypEvChain
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.IntWOfPow
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypFin
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.Bundle0006

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ.PValIntN Formalism.MainNotions.G.CmpJ.PInvLe
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

section Step

variable {j : ℕ} (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}


set_option maxHeartbeats 2000000 in
structure StepTies (Fo : FormsIn M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch) (Gt : GatTies D) (c : LatCmp D) : Prop where

  frRat : ∀ β, FrRatJ (Lc.t β) Lc.B

  sameU : ∀ β, SameUlocJ hj (Fo.K β).lev (Lc.Uloc β)

  hypT : ∀ β, HypTJ (Lc.t β)

  bad_p : ∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal

  std : cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 * gramN D (j + 1) hj *
    (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 = 1

  psi : ∀ β, UnitCharacterChartCompatibility hj (Fo.K β).lev (c.embW u w h) (Lc.ψ β)

  chRat : ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)

  hypC : ∀ β, HypTJC (Lc.t β)

  ok : Fo.okW w

  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T

  Lb_eq : ∀ β, (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) (Lc.Lb β)

variable {hj} {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}
  {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X0 u w h Lv j Fo.Ch}

theorem StepTies.chi (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) (κ : (Fo.K β).lev.U) :
    ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧ D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ) :=
  chiUnit_of hj (Fo.K β).lev (S.sameU β) (c.embW u w h) (S.psi β) S.bad_p (fun x => c.embW_int u w h x) κ


set_option maxHeartbeats 4000000 in
theorem StepTies.ties (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LocTiesR hj Fo Lc (c.embW u w h) β :=
  { frRat := S.frRat β
    sameU := S.sameU β
    hypT := S.hypT β
    bad_p := S.bad_p
    std := S.std
    psi := S.psi β
    chiRat := fun κ => let ⟨r, _, _, hr⟩ := S.chi β κ; ⟨r, hr⟩
    chRat := S.chRat β }

theorem StepTies.lat (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LatTies hj w Fo β (Lc.Lb β) :=
  { siteGood_prime_torsion := S.siteGood_prime_torsion
    Lb_eq := S.Lb_eq β
    lat := fun cl => isLattice_chart (Fo.K β) cl
    chi := S.chi β }

theorem StepTies.core (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).Core (c.embW u w h) β :=
  core_of_R hj K ht hF (S.ties β)

theorem StepTies.valIntN (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).ValIntN (c.embW u w h) w := by
  have ties (β : Fo.Ch) : LocTies hj Fo Lc (Gt.gat_pos u w h) (c.embW u w h) β :=
    { frRat := S.frRat β
      sameU := S.sameU β
      hypT := S.hypT β
      bad_p := S.bad_p
      std := S.std
      pos_emb := fun v s x => locJ_pos_emb hj (Lc.t β) Lc.B K v s x
      wt := StepIn.wt_of (M := M) Gt w h Lv ht hF j hj (stepInOf hj Fo Lc (Gt.gat_pos u w h)) rfl β
      psi := S.psi β
      chiRat := (S.ties β).chiRat
      chRat := S.chRat β }
  exact valIntN_rec hj (c.embW u w h) ties Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    ((D.gat u w h).P.setting (plc Gt u w h)).frac_O (fun x => c.embW_int u w h x) S.lat

theorem StepTies.twUnit (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).TwUnit w β := by
  have lat : LatIn (stepInOf hj Fo Lc (Gt.gat_pos u w h)) w β :=
    { prime := h.1
      resChar := rfl
      siteGood_prime_torsion := S.siteGood_prime_torsion
      alg := fun v a => (X0.g u w h).spl_alg _ ((X0.g u w h).pl v).2 a
      base := fun v t =>
        Formalism.L2.G.RelativeIndexFlags.frlat_re (rankN D (j + 1) hj) ((X0.g u w h).pl v).1
          ((X0.g u w h).spl _ ((X0.g u w h).pl v).2) (Lc.Lb β) Lc.B
          ((Lc.t β).fr _ ((X0.g u w h).pl v).2) (S.frRat β _ _) ((Lc.t β).fr_lat _ ((X0.g u w h).pl v).2)
          (Fo.K β).lev.Lb (S.Lb_eq β) t
      lat := (S.lat β).lat
      chi := S.chi β }
  exact twUnit_of (stepInOf hj Fo Lc (Gt.gat_pos u w h)) (c.embW u w h) w β (S.core K ht hF β)
    (fun x => c.embW_int u w h x) lat

theorem StepTies.chX (S : StepTies hj Fo Lc Gt c) : ChX (stepInOf hj Fo Lc (Gt.gat_pos u w h)) := by
  have charts : ChX (stepInOf hj Fo Lc (Gt.gat_pos u w h)) := by
    refine { hypC := ?_, inj := ?_, onto := ?_, cinj := ?_ }
    all_goals
      intro β
      let : Fintype (Lc.cmpt β) := Lc.fin β
    · exact locHypC_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β) (S.frRat β) (S.hypC β)
    · exact fun a => gamI_inj_locJ hj (Lc.t β) Lc.B a
    · exact fun a => gamOnto_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β) a
    · exact compInj_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β)
  exact charts

end Step

structure HypTiesI (X0 : Formalism.L2.Herm.Herm0 D) (I : CmpJIn Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where

  fl_t : Fl.t = D.R.t

  fill : FillTie Gt u w h Fl

  step : ∀ j hj, ∃ (Fo : FormsIn (I.at' j hj).M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch),
    (I.at' j hj).st = stepInOf hj Fo Lc (Gt.gat_pos u w h) ∧ StepTies hj Fo Lc Gt c

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem HypTiesI.chX {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (I.at' j hj).st := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.chX

theorem HypTiesI.core {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    ∀ β, (I.at' j hj).st.Core (c.embW u w h) β := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.core K A.fl_t A.fill

theorem HypTiesI.fin {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    (gatJ Lv (j + 1)).FinClasses :=
  finClasses_of (S := (I.at' j hj).st) (A.core K j hj) (A.chX j hj)

theorem HypTiesI.hyp {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c I :=
  cmpJHyp_of_two c Gt Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    (A.core K)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.ok)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.twUnit K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.valIntN K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact iwF_of hj Fo Lc (Gt.gat_pos u w h))
    (A.fin K) A.chX
    (fun j hj => formsOnClassOf _)
    (fun j hj => Formalism.MainNotions.G.CmpJ.PEvValChain.cmpLiftOf_holds _ _)

structure HypTies (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where
  fl_t : Fl.t = D.R.t
  fill : FillTie Gt u w h Fl
  step : ∀ j hj, StepTies hj (Z.Fo j hj) (Z.Lc j hj) Gt c

theorem HypTies.toI {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) : HypTiesI X0 (Z.I Gt) Gt c :=
  { fl_t := A.fl_t
    fill := A.fill
    step := fun j hj => ⟨Z.Fo j hj, Z.Lc j hj, rfl, A.step j hj⟩ }

theorem HypTies.hyp {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c (Z.I Gt) := A.toI.hyp K

theorem HypTies.atHyp {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) (K : CmpTied D X0 T Gt c) : AtHyp Z Gt c :=
  { fl_t := A.fl_t
    fill := A.fill
    ties := fun j hj => (A.step j hj).ties
    hypC := fun j hj => (A.step j hj).hypC
    ok := fun j hj => (A.step j hj).ok
    twUnit := fun j hj => (A.step j hj).twUnit K A.fl_t A.fill
    valIntN := fun j hj => (A.step j hj).valIntN K A.fl_t A.fill
    fin := A.toI.fin K
    card := (A.hyp K).card }

section Fam

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}

end Fam

end Formalism.MainNotions.G.ChF

end
