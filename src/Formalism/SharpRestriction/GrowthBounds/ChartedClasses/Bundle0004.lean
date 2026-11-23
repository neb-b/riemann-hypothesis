module

public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTwLat
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0008
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0015

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.BasesAtSpec
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.UG
open scoped TensorProduct

namespace Formalism.MainNotions.G.KAat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E}

end Re

section AtS

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))


end AtS

section Spec

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D}


end Spec

end Formalism.MainNotions.G.KAat

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TieStabKaAtAny
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
  {I : CmpJIn Tw u μ w h Lv}

theorem tieStab_kaAtAny [Fact (D.what₂.places.resChar w).Prime] (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv) (hCh)
    (std) (vp) (unif) (eO) (eO_spec) (dG) (dG_spec) (om) (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (hU : DV.Used D μ) (hS0 : OrbitPlaces.Stab0 D) (j : ℕ) (hj : j ≤ D.R.m) : TieStabAt (Y := Y) u μ (kaAtAny X H Gt Ch hCh).cls j :=
  Formalism.L2.KerInert.SecondKernelStabilizers.stabilizer_any_level D c Tw u μ w h Fl Lv (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt Ch hCh std vp unif eO
    eO_spec dG dG_spec om Y hU hS0 j hj

end Formalism.MainNotions.G.KAat

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure AtIn where
  Fo : ∀ j (hj : j + 1 ≤ D.R.m), FormsIn (Tw.fm u μ) (j + 1) hj
  Lc : ∀ j (hj : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (Fo j hj).Ch

variable {X0 Tw u μ w h Lv}

def AtIn.st (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1)) :=
  stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h)

def AtIn.I (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) : CmpJIn Tw u μ w h Lv := inTw (Z.st Gt)

structure AtHyp (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where
  fl_t : Fl.t = D.R.t
  fill : FillTie Gt u w h Fl
  ties : ∀ j hj β, LocTiesR hj (Z.Fo j hj) (Z.Lc j hj) (c.embW u w h) β
  hypC : ∀ j hj β, HypTJC ((Z.Lc j hj).t β)
  ok : ∀ j hj, (Z.st Gt j hj).okW w
  twUnit : ∀ j hj β, (Z.st Gt j hj).TwUnit w β
  valIntN : ∀ j hj, (Z.st Gt j hj).ValIntN (c.embW u w h) w
  fin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses
  card : ∀ j (hj : j + 1 ≤ D.R.m), Fintype.card ((Tw.fm u μ).lat (j + 1)).ι = Module.finrank (D.gat u w h).O (gatJ Lv (j + 1)).M

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem AtHyp.chX {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (((Z.I Gt).at' j hj).st) :=
  chX_stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h) (fun β => (A.ties j hj β).sameU) (fun β => (A.ties j hj β).frRat)
    (A.hypC j hj)

end Formalism.MainNotions.G.KAat

end
end

