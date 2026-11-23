module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

structure XPart (D : D7) (u : D.what₂.Word) where
  c : GlobalTheory.ChainOnto.Com D
  top : StAt D.sp.X'
  x : ∀ j, DefSp (D.sp.X j)
  k : ∀ j, KerDat (D.sp.X j) (D.sp.X (j + 1))
  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz
  Ram : ∀ j, Submodule ℂ (Col D u j)
  rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ
  eT : (D.mem u).P.Mt →ₗ[ℂ] top.st.CC c

@[reducible] def XPart.geo (a : XPart D u) (bot : StAt (D.sp.Y 0)) (mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D) : Geo D := ⟨a.c, bot, mid, a.top⟩


set_option maxHeartbeats 1000000 in
structure YPart (a : XPart D u) where
  bot : StAt (D.sp.Y 0)
  mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D
  p : ∀ j, GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st j) ((a.geo bot mid).st (j + 1))
  pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st (j + 1)) a.top.st
  t : ∀ j, GA D ((a.geo bot mid).st j).V
  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt ((a.geo bot mid).st j).V (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt ((a.geo bot mid).st (j + 1)).V (D.sp.X (j + 1)) ρ
  sBF : ∀ j ρ h, StepBF a.c.ψ ((bes j ρ h).lev (a.x j).vol) ((jac j ρ h).lev (a.x (j + 1)).vol)
  sFB : ∀ j σ h, StepFB a.c.ψ ((jac j (σ + 1) h).lev (a.x (j + 1)).vol)
    ((bes (j + 1 + 1) σ (idx_step h)).lev (a.x (j + 1 + 1)).vol)
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (a.x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

section Off

open GlobalTheory.FinPl

structure OffX (a : XPart D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k
  I : List ι
  q : Unif k
  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1
  β : ∀ j i, Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)
  Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)
  cT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  ζ₀ : Fin a.Lz.rank → D.host.E
  γ : ∀ i, Frame (p i) D.sp.X' (Fin D.sp.X'.rank)
  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (D.sp.X n) (Fin D.sp.X'.rank ⊕ Fin 1)

variable {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def OffX.atT (o : OffX a k ι) (v : Pl D) : Prop := ∃ i, v = (o.p i).v

end Off

section AtLevel

open GlobalTheory.LocMod

structure GX (a : XPart D u) (ζ₀ : Fin a.Lz.rank → D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar a.c.ψ S.ψ
  mu : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (a.c.chS j)⁻¹ (S.μ j)
  FX : ∀ j, j ≤ s + 1 → Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  z₀ : Fin a.Lz.rank → k
  z₀_unit : ∃ c : k, valuation k c = 1 ∧ z₀ = c • fun i => (ofSplit q).pr (ζ₀ i)
  last : FM.β = fromCols ((a.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((a.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X j) (a.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (a.x (s + 1 + 1)).L (· = q.v)
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 a.top.β (FT.β.submatrix id e.symm)
  cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt a.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)
  cg_pen : (ofSplit q).IsCombAt a.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt a.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GX.fld GX.val GX.top GX.loc GX.mea GX.bor

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

end AtLevel

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {v : B.Word}
  (a : XPart (I.rec7 l Z) v) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

end World

end GlobalTheory.SeeSaw

end
