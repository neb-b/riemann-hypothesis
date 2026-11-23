module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

structure XGeo (D : D7) where
  x : ∀ j, DefSp (D.sp.X j)
  vac : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) → ℂ
  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz
  ζ₀ : Fin Lz.rank → D.host.E
  bT : GA D D.sp.X'
  LT : GlobalTheory.FinPl.Lat D.sp.X'


set_option maxHeartbeats 1000000 in
structure YRat (a : XGeo D) where
  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (a.x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank
  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E

structure YMeas {a : XGeo D} (y : YRat a) where
  vol : ∀ j, Vol (Yc D j)
  volT : Vol D.sp.X'
  μf : ∀ j, Measure (GfC (Yc D j))
  μT : Measure (GfC D.sp.X')
  ρJ : ∀ j ρ h, Measure ((jacGrp (y.jac j ρ h).d).subgroupOf (GfC (Yc D (j + 1))))
  ρB : ∀ j ρ h, Measure ((besGrp (y.bes j ρ h).d (y.bes j ρ h).o).subgroupOf (GfC (Yc D j)))
  κ : ℕ → ℝ

@[reducible] def mkGeo {a : XGeo D} {y : YRat a} (m : YMeas y) (b : ∀ j, GA D (Yc D j)) : Geo D :=
  ⟨m.vol, m.volT, a.x, a.vac, y.bes, y.jac, y.lnk, y.vL, a.Lz, a.oT, m.μf, m.μT, m.ρJ, m.ρB, m.κ, b, a.bT, a.LT⟩

def YRat.Tau {a : XGeo D} (y : YRat a) (lam : D.host.E) : Prop :=
  ∀ j h, (y.τ j h)ᴴ * ((y.bes j 0 h).L.gram * y.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • a.Lz.gram ∧
    y.τ j h *ᵥ a.ζ₀ = lam • (y.bes j 0 h).ζ

structure LocX (a : XGeo D) (βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)) (PP : Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  under : q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  FX : ∀ j, j ≤ s + 1 → Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)

  last : FM.β = fromCols ((a.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((a.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ fun i => (ofSplit q).pr (a.ζ₀ i)) r)
  latX : ∀ j hj, IntIn q (D.sp.X j) (FX j hj) (a.x j).L
  latM : IntIn q (D.sp.X (s + 1 + 1)) FM (a.x (s + 1 + 1)).L
  latT : IntIn q D.sp.X' FT a.LT
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' a.bT βT (FT.β.submatrix id e.symm)

attribute [instance] LocX.fld LocX.val LocX.top LocX.loc LocX.mea LocX.bor

structure LocY {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (y : YRat a)
    (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (β : ∀ j, GL (Fin (Yc D j).rank) (Lev.EAf D)) (b : ∀ j, GA D (Yc D j))
    (bas : ∀ j c, j + c = l.s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) l.k) where
  FY : ∀ j c, j + c = l.s + 1 → Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)
  sc : ℕ → l.k
  sc_unit : ∀ j, valuation l.k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit l.q).xi
  hz_unit : ∀ j ρ h, valuation l.k ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1
  bes : ∀ j ρ h c (hc : j + c = l.s + 1), (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j (by omega)) (FY j c hc)
  jac : ∀ j ρ h c (hc : j + 1 + c = l.s + 1), (ofSplit l.q).IsJacFrame ((y.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (l.FX (j + 1) (by omega)) (FY (j + 1) c hc)
  tau : ∀ h, (y.τ l.s h).map (ofSplit l.q).pr *ᵥ (fun i => (ofSplit l.q).pr (a.ζ₀ i)) =
    (-((ofSplit l.q).xi * sc l.s)) • fun i => (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i)
  latY : ∀ j c hc, IntIn l.q (Yc D j) (FY j c hc) (N j)
  frame : ∀ j c (hc : j + c = l.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (l.s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit l.q) (Yc D j) (b j) (β j)
      (((FY j c hc).β * (bas j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i))

section Real

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

def QAll (PP : Pl D.host.E) : Prop := ∃ t, PP ∈ (pk W).Q t

structure PkHyp : Prop where
  bot : GlobalTheory.MiTop.BotHyp W
  lev : LevHyp W
  ex : (pk W).ExAt
  hTop : ∀ t, LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e) =
    MultT (pk W).θ (pk W).MX (levS _ (pk W).βX ((pk W).datXt t)) (levChi _ (pk W).βX ((pk W).datXt t))
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  fin : Finite W.P.T

  sel : ∀ PP PP', QAll W PP → QAll W PP' → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP'

  aa : ∀ PP : Pl D.host.E, (QAll W PP ∨ PP ∈ (pk W).Pg ∨ ∃ u, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

variable {W} {u : D.what₂.Word} (f : FamCh W u)

structure VTie (v : VCom f.c) : Prop where
  b : ∀ j, v.b j = f.g.b j
  bT : v.bT = f.g.bT ∧ v.NT = f.g.LT
  gP : ∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  tP : ∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal
  moves : ∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
    GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((pk W).ΛY j) (v.N j) P
  movesT : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (pk W).ΛX f.g.LT P
  Ψ : ∀ j, j + 1 < D.R.m → ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P a a', v.Ψ j P a a' = comb f.c.ψ _ _ o
    ((pk W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1))
      (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))
  ΨT : ∀ j h, ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P, v.ΨT j h P = comb f.c.ψ _ _ o
    (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))
  nz : (∀ j, j + 1 < D.R.m → ∃ P, v.Ψ j P 1 1 ≠ 0) ∧ ∀ j h, ∃ P, v.ΨT j h P ≠ 0

structure GRead {v : VCom f.c} {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg) : Prop where
  idem : ∀ i, Formalism.L2.NTheta.IsIdemAt (G i).q.e (pl i).1 ∧ (G i).q.v = (pl i).1.under (𝓞 D.host.F)
  mu : ∀ i j, 1 ≤ j → j ≤ D.R.m → (ofSplit (G i).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ ((G i).S.μ j)
  frame : ∀ i j c (hc : j + c = (G i).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) (Yc D j) (f.g.b j) ((pk W).βY j)
      ((((G i).FY j c hc).β * (((G i).S.T (Fin D.R.t)).bas j c hc).val).submatrix id
        fun a => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm a))
  frameTop : ∀ i, ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) ((G i).s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) D.sp.X' f.g.bT (pk W).βX ((G i).FT.β.submatrix id e.symm)

  lev : ∀ (g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1)),
    (g ∈ (lvP W).H ↔ ∀ i, ∃ x : (G i).S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) ∧
    ∀ (hg : g ∈ (lvP W).H) (x : ∀ i, (G i).S.P.J), (∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) →
      (lvP W).chi ⟨g, hg⟩ = ∏ i, (G i).S.P.lam (x i)

end Real

section True

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True

end GlobalTheory.Fam

end
