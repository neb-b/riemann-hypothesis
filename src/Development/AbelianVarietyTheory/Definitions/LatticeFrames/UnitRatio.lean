module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

def UnitRatio (S : ℕ → Prop) (x y : ℂ) : Prop :=
  y ≠ 0 ∧ ∃ n : ℕ, 0 < n ∧ ∃ r : ℚ, r ≠ 0 ∧ (x / y) ^ n = (r : ℂ) ∧ ∀ p : ℕ, p.Prime → padicValRat p r ≠ 0 → S p

structure Base (c : Comm D) where
  Λ : ∀ j, GlobalTheory.FinPl.Lat (c.V j)
  β : ∀ j, GL (Fin (c.V j).rank) (Lev.EAf D)
  b : ∀ j, GA D (c.V j)

  ΛT : GlobalTheory.FinPl.Lat c.T
  βT : GL (Fin c.T.rank) (Lev.EAf D)
  bT : GA D c.T
  LT : GlobalTheory.FinPl.Lat c.T
  Pg : Finset (Formalism.L2.DIV.Pl D.host.E)
  P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ

variable {c : Comm D}


open Classical in
def Base.S (B : Base c) : Finset (GlobalTheory.FinPl.Pl D) := B.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

section Off

open GlobalTheory.FinPl

structure Off (B : Base c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k

  I : List ι

  q : Unif k

  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (c.X j) (Fin (c.X j).rank)

  Q : ∀ j, ι → Pair k (Fin (c.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)

  L : ∀ j, Lat (c.V j)

  M : ∀ j ρ h, Lat (c.bes j ρ h).V₀

  cT : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  cG : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E

  ζ₀ : Fin c.Lz.rank → D.host.E

  γ : ∀ i, Frame (p i) c.T (Fin c.T.rank)

  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (c.X n) (Fin c.T.rank ⊕ Fin 1)

variable {B : Base c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : Off B k ι)

namespace Off

end Off

end Off

section AtLevel

open GlobalTheory.LocMod

structure GAt (B : Base c) (τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) where
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
  char : (ofSplit q).IsChar c.ψ S.ψ
  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j cc, j + cc = s + 1 → Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin cc)
  sc : ℕ → k
  sc_unit : ∀ j, valuation k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1
  bes : ∀ j ρ h cc (hc : j + cc = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j cc hc)
  jac : ∀ j ρ h cc (hc : j + 1 + cc = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j)
    ((ofSplit q).hz (c.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) cc hc)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X j) (c.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X (s + 1 + 1)) (c.x (s + 1 + 1)).L (· = q.v)
  frame : ∀ j cc (hc : j + cc = s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) j ≃ Fin (c.V j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) (c.V j) (B.b j) (B.β j)
      (((FY j cc hc).β * ((S.T (Fin D.R.t)).bas j cc hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j cc hc (e.symm i))
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin c.T.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) c.T B.bT B.βT (FT.β.submatrix id e.symm)
  cg : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j cc (H : j + 1 + cc = s), (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j cc H 1 1)
  cg_pen : (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GAt.fld GAt.val GAt.top GAt.loc GAt.mea GAt.bor

variable {B : Base c} {τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E}

end AtLevel



end GlobalTheory.Fam

end
