module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
section
noncomputable section

namespace GlobalTheory.TwV.Xc

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV GlobalTheory.TwV
open GlobalTheory.TwU (ratA ssRec)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} {t : KerEntTied ex}

def KIn (t : KerEntTied ex) : Prop := ∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y

abbrev A0 (J : Joint t H X) : LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w hg) := (lev0At J.Gd u w hg).A

def Spl (J : Joint t H X) : Prop := SplAlg (A0 J) ∧ ∀ j hj β, SplAlg ((I.at' j hj).st.loc β)


open Classical in
def chiI (J : Joint t H X) (x : (AfE D.host.F D.host.E)ˣ) : ℂ :=
  if h : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x then ((D.chiD (J.dtU h.choose) : ℂˣ) : ℂ) else 0

def IsUnifAt (J : Joint t H X) (v : Fin (D.gat u w hg).P.nV) (π : (AfE D.host.F D.host.E)ˣ) : Prop :=
  π ∈ U1 (sigD D) ∧ OneOff ((A0 J).pl v).1 π ∧ ordA (A0 J) v π = 1

variable [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X)

def MoveBy (j : ℕ) (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ)
    (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj).K (J.chart std j hj (c, La))).lev.U) : Prop :=
  g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ∧
  (J.pt std j hj (c, ((sysS H X std).Lv.lev j c).smul γ La)).1 = ratA D.host.F g * (J.pt std j hj (c, La)).1 * κ.1 ∧
  (∀ (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (v : (sysS H X std).Pl),
    (J.fd std).frM j (c, La) v * (gamAt (sysS H X std) j c γ v : Matrix _ _ _) =
      (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj) g).map (J.rho std v) * (J.fd std).frM j (c, La) v) ∧
  ∃ r : D.what₂.LL, D.what₂.embLL r = ((((J.St j hj).K (J.chart std j hj (c, La))).lev.chi κ : ℂˣ) : ℂ) ∧
    algebraMap (sysS H X std).G.O (sysS H X std).G.Kf ((((sysS H X std).Lv.lev j c).χ γ : (sysS H X std).G.Oˣ) : (sysS H X std).G.O) =
      ex.cmp.embW u w hg r

def FillAt (j : ℕ) (hj : j < D.R.m) : Prop :=
  ∀ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) → ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)),
    (sysS H X std).w v (j + 1) s = e (hT.gat_pos u w hg ⟨v, s⟩) - ((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) -
      (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)

def SameAway (v : (sysS H X std).Pl) (j : ℕ) (La Lb : (sysS H X std).Lt j) : Prop :=
  ((sysS H X std).Pj j).IsLatTup La.2 ∧ ((sysS H X std).Pj j).IsLatTup Lb.2 ∧ La.1 = Lb.1 ∧
    Function.update La.2 ((sysS H X std).vJ j v) ⊥ = Function.update Lb.2 ((sysS H X std).vJ j v) ⊥


omit [Fact (D.what₂.places.resChar w).Prime] in
def Sites (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X}, J.At std → Prop) : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X} (S : J.At std), J.Dict std → Spl J → Q S

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
section
noncomputable section

namespace GlobalTheory.TwV.DelB

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference
open GlobalTheory.TwU (StepCharts ChainCharts AdData ratA ssRec toStdCo pPow scal0 xiM)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7}

def tay {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) : MvPowerSeries (D.what₂.Tau × Fin b × Fin a) ℂ := fun α => TaylorLogMetric.taylor D G α


open Classical in
def pullMat {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E)
    (x y : D.what₂.Tau × Fin b × Fin a) : ℂ :=
  if x.1 = y.1 then (starRingEnd ℂ) (TaylorLogMetric.embT D x.1 (e' y.2.1 x.2.1)) * TaylorLogMetric.embT D x.1 (e y.2.2 x.2.2) else 0

def reV {a b N N' : ℕ} (ha : a = N) (hb : b = N') (G : TaylorLogMetric.VC D N N' → ℂ) : TaylorLogMetric.VC D a b → ℂ :=
  fun z => G fun τ i k => z τ (Fin.cast hb.symm i) (Fin.cast ha.symm k)

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

def reframe (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) : FData X D :=
  { fd with frM := fun j La v => (star (e j La)).map (ρ v) * fd.frM j La v }

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}


open Classical in
def thCl (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
  if h : (X.Pj j).m + 1 = D.R.N j ∧ (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) then
    reV h.1 h.2 ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2))
  else 0

def TieOpS {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) {ι : ℂ →+* Y.Kc} (sO : ∀ j, X.Lt j → Y.Kc) (j : ℕ)
    (e : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, K2.SharpQ t ex.tw u μ j x Q → ∀ n : X.ZA j →₀ ℕ,
    AddMonoidAlgebra.coeff (polDel X Y.Kc j (Gm j La x)) n =
      sO j La • AddMonoidAlgebra.coeff (trDY X Y.Kc j D e Φ₀ (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))) n

end Gen

section Site

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Dec where
  gam : ∀ j (_ : j ≤ D.R.m), (sysS H X std).Lt j → GL (Fin (D.R.N j)) D.host.E
  kap : ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((J.St j hj).K (J.chart std j hj La)).lev.U
  mem : ∀ j hj La, gam j hj La ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj)
  eq : ∀ j hj (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 →
    (J.pt std j hj La).1 = ratA D.host.F (gam j hj La) * ((J.St j hj).y (clsAt X H j La.1 La.2)).1 * (kap j hj La).1

def gMat (j : ℕ) (hj : j ≤ D.R.m) (γ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E :=
  LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj) (J.A.crd j hj)).trans
    (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj) γ)).toLinearMap

variable {J std} (d : Dec J std)


open Classical in
def Dec.eM (j : ℕ) (La : (sysS H X std).Lt j) :
    Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E :=
  if h : j ≤ D.R.m ∧ ((sysS H X std).Pj j).m + 1 = D.R.N j then
    (gMat J j h.1 (d.gam j h.1 La)).submatrix (Fin.cast h.2) (Fin.cast h.2)
  else 1

def Dec.fd2 : FData (sysS H X std) D := reframe (J.fd std) (J.rho std) d.eM

def Dec.chi (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : ℂ :=
  ((((J.St j hj).K (J.chart std j hj La)).lev.chi (d.kap j hj La) : ℂˣ) : ℂ)

variable (S : J.At std)

def Dec.sP (j : ℕ) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) : ℂ :=
  if h : j + 1 ≤ D.R.m then
    S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap j (Nat.le_of_succ_le h) La).1) * d.chi (j + 1) h La' /
      (S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap (j + 1) h La').1) * d.chi j (Nat.le_of_succ_le h) La)
  else 0

def Dec.sC (j : ℕ) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) : ℂ :=
  scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' *
    (Base.chiFac t.χ _ _ ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La'))⁻¹ * d.sP S j La La'

def Dec.sH (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) :
    ℂ_[D.what₂.places.resChar w] :=
  pPow (sysS H X std) j La La' * ι (d.sC S j La La')

def Dec.gS (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) :
    MvPowerSeries (D.what₂.Tau × Fin (((sysS H X std).Pj (j + 1)).m + 1) × Fin (((sysS H X std).Pj j).m + 1)) ℂ_[D.what₂.places.resChar w] :=
  d.sH S ι j La La' • MvPowerSeries.map ι (tay (thCl (X := sysS H X std) t u μ (clsAt X H) j La La'))

def Dec.uS (j : ℕ) (La : (sysS H X std).Lt j) : ℂ :=
  if h : j ≤ D.R.m then
    (d.chi j h La)⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F (d.gam j h La))))⁻¹ *
      (∏ τ, TaylorLogMetric.embT D τ (gMat J j h (d.gam j h La)).det) ^ (((D.R.N (j + 1) / 2 : ℕ) : ℤ) + cTw D j) *
      ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ (-(cTw D j))
  else 0

def Dec.uT (j : ℕ) (La' : (sysS H X std).Lt (j + 1)) : ℂ :=
  if h : j + 1 ≤ D.R.m then
    d.chi (j + 1) h La' * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F (d.gam (j + 1) h La'))) *
      (∏ τ, TaylorLogMetric.embT D τ (gMat J (j + 1) h (d.gam (j + 1) h La')).det) ^ (-(((D.R.N j / 2 : ℕ) : ℤ) + cTw D (j + 1))) *
      ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ cTw D (j + 1)
  else 0

def Dec.PullAt (j : ℕ) : Prop :=
  ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
    ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → ∀ z,
    kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La')
        (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') z =
      d.sP S j La La' * TaylorLogMetric.pull D t.B.tor (d.eM j La) (d.eM (j + 1) La') (thCl (X := sysS H X std) t u μ (clsAt X H) j La La') z

def Dec.SerAt (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) : Prop :=
  ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
    ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 →
    FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT) j La La' =
      linSub (fun x y => ltC S.g S.hLT * subBG S.E.toCEmb (hT.gat_pos u w hg) d.fd2 j La La' x y) (d.gS S ι j La La')

def Dec.ScalAt (j : ℕ) : Prop :=
  ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
    ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 →
    d.sC S j La La' = ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) * d.uS S j La * d.uT S j La'

end Site

end GlobalTheory.TwV.DelB

end
end

