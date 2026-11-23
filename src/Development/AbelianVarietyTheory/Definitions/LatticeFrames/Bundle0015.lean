module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  ∑ u ∈ c.support, c u • heisO ψ S T u f

def IsFinComb {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, u.map (infPart D) = 0

def biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => comb ψ S A' c' (C u') v) u

structure IsBiVac (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  left : ∀ v, IsThetaFunO ψ A S (fun u => C u v) ∧ IsLatVac (heisO ψ A S) (latO A S LA LS fun _ => True) fun u => C u v
  right : ∀ u, IsThetaFunO ψ S A' (C u) ∧ IsLatVac (heisO ψ S A') (latO S A' LS LA' fun _ => True) (C u)

def JointSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

def biLift {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S A' → ℂ) (h₂ : GA D A') : ℂ :=
  ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 ∂vA.μ) ∂vS.μ

def HasCen (A : HSp D) (χ : GA D A → ℂ) (φ : GA D A → ℂ) : Prop :=
  ∀ z ∈ GinfC A, z ∈ Subgroup.center (GA D A) → ∀ h, φ (h * z) = χ z * φ h

def InCell {V : HSp D} (R : Subgroup (GA D V)) (t : GA D V) (J : Set (GA D V)) (h : GA D V) : Prop :=
  ∃ r ∈ R, ∃ a ∈ GinfC V, ∃ k ∈ J, h = r * a * t * k

structure DefSp (V : HSp D) where
  s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  vol : Vol V

structure DefSp.Is {V : HSp D} (x : DefSp V) : Prop where
  sig : V.SigOK
  cpt : CoCpt V
  cart : ∀ τ, IsCartanInv (gramAt D V τ) (x.s τ)
  pm : ∀ τ, x.s τ = 1 ∨ x.s τ = -1
  onb : ∀ τ, ∃ p, IsONBasis (gramAt D V τ) (x.s τ) (x.B τ) p
  sd : IsSelfDualC V x.L

structure KerDat (S T : HSp D) where
  om : Om S T
  vac : WO S T → ℂ
  c : WO S T →₀ ℂ

structure KerDat.Is (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T) :
    Prop where
  weil : ∃ χS χT, IsWeilDatumO ψ S T χS χT k.om
  vac : IsVacO ψ θ S T x.s y.s x.L y.L k.vac
  fin : IsFinComb k.c

def KerDat.pt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) : WO S T → ℂ :=
  pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T k.c k.vac) P

def KerDat.lift (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (x : DefSp S) (y : DefSp T) (k : KerDat S T)
    (P : PolF D T.rank S.rank) (φ : GA D S → ℂ) : GA D T → ℂ :=
  liftT k.om x.vol.μ x.vol.𝓕 φ (k.pt ψ θ x y P)

def FockReduce (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'),
    x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
    ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → JointSmooth C →
      ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank),
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ)

structure BesAt (V A : HSp D) (ρ : ℕ) where
  V₀ : HSp D
  L : HSp D
  d : HypDec V V₀ ρ
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vN : VolN d

@[reducible] def BesAt.lev {V A : HSp D} {ρ : ℕ} (b : BesAt V A ρ) (vA : Vol A) : BesLev D ρ :=
  ⟨V, b.V₀, A, b.L, b.d, b.o, b.ζ, b.line, b.cpt, vA, b.vN⟩

structure JacAt (W W₀ : HSp D) (ρ : ℕ) where
  d : HypDec W W₀ ρ
  cpt : CoCpt W₀
  vN : VolN d

@[reducible] def JacAt.lev {W W₀ : HSp D} {ρ : ℕ} (b : JacAt W W₀ ρ) (v0 : Vol W₀) : JacLev D ρ :=
  ⟨W, W₀, b.d, b.cpt, v0, b.vN⟩

open GlobalTheory.ChainOnto (Com PiLocalization₂)

structure StAt (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

@[reducible] def StAt.st {V : HSp D} (a : StAt V) : PiLocalization₂ D := ⟨V, a.par, a.M, a.Λ, a.β, a.L, a.ν, a.fd⟩

structure Geo (D : D7) where
  c : Com D
  bot : StAt (D.sp.Y 0)
  mid : ℕ → PiLocalization₂ D
  top : StAt D.sp.X'

def Geo.st (g : Geo D) : ℕ → PiLocalization₂ D
  | 0 => g.bot.st
  | j + 1 => g.mid j

abbrev Col (D : D7) (u : D.what₂.Word) (j : ℕ) : Type := (D.mem u).C.cls j → (D.mem u).C.Y j → ℂ

theorem idx_step {j σ m : ℕ} (h : j + 2 * (σ + 1) + 2 = m) : j + 1 + 1 + 2 * σ + 2 = m := by omega


set_option maxHeartbeats 1000000 in
structure Dat (D : D7) (u : D.what₂.Word) extends Geo D where

  p : ∀ j, GlobalTheory.ChainOnto.Step c (toGeo.st j) (toGeo.st (j + 1))
  pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step c (toGeo.st (j + 1)) top.st

  t : ∀ j, GA D (toGeo.st j).V

  x : ∀ j, DefSp (D.sp.X j)
  k : ∀ j, KerDat (D.sp.X j) (D.sp.X (j + 1))

  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (toGeo.st j).V (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (toGeo.st (j + 1)).V (D.sp.X (j + 1)) ρ
  sBF : ∀ j ρ h, StepBF c.ψ ((bes j ρ h).lev (x j).vol) ((jac j ρ h).lev (x (j + 1)).vol)
  sFB : ∀ j σ h, StepFB c.ψ ((jac j (σ + 1) h).lev (x (j + 1)).vol) ((bes (j + 1 + 1) σ (idx_step h)).lev (x (j + 1 + 1)).vol)
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz

  Ram : ∀ j, Submodule ℂ (Col D u j)
  S : ∀ j, Col D u j →ₗ[ℂ] Col D u j
  rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ

  eT : (D.mem u).P.Mt → top.st.CC c

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

abbrev B (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) : BesLev D ρ := (d.bes j ρ h).lev (d.x j).vol

abbrev lev (j : ℕ) : Set (GA D (d.st j).V) := levS (d.st j).V (d.st j).β (d.st j).L

structure Base : Prop where
  com : d.c.Is
  st : ∀ j, j < D.R.m → (d.st j).Is d.c j
  top : d.top.st.Is d.c D.R.m
  p : ∀ j, j + 1 < D.R.m → (d.p j).Is (j + 1)
  pT : ∀ j h, (d.pT j h).Is D.R.m
  t : ∀ j, d.t j ∈ GfC (d.st j).V
  x : ∀ j, j ≤ D.R.m → (d.x j).Is
  k : ∀ j, j < D.R.m → (d.k j).Is d.c.ψ d.c.θ (d.x j) (d.x (j + 1))
  sBF : ∀ j ρ h, (d.sBF j ρ h).om = (d.p j).ω ∧ (d.sBF j ρ h).vW.μ = (d.st (j + 1)).ν ∧ (d.sBF j ρ h).vW.𝓕 = (d.st (j + 1)).fd
  sFB : ∀ j σ h, (d.sFB j σ h).om = (d.p (j + 1)).ω ∧ (d.sFB j σ h).vW.μ = (d.st (j + 1 + 1)).ν ∧
    (d.sFB j σ h).vW.𝓕 = (d.st (j + 1 + 1)).fd

end Dat

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParBoundW (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank ((s.V.rank : ℝ) / 2)

def ChainLW (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
  ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)

def Com.eps {D : D7} (c : Com D) (k : ℕ) : (AE D)ˣ →* Circle := if Odd k then c.η⁻¹ else 1

def ChainUp (D : D7) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ D.R.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → s.Is c k ∧
      ∀ ipD₀ ip₀ ipD ip, IsMet c s₀ ipD₀ ip₀ → IsMet c s ipD ip → ∀ (u : s₀.CC c) B, IsPar u B →
        ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k)

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
section
noncomputable section

namespace GlobalTheory.Core.Rk.Exh

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def under (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Finset (FinPl D) := Z.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def prinDat (A : HSp D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Formalism.L2.DIV.LevDat D.host.E ℂ A.rank :=
  Formalism.IndefR.Lev.datW A.rank Z (Formalism.L2.DIV.LevelP.triv _ _ _) Formalism.IndefR.Lev.Frm.B

def prin (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Subgroup (GA D A) :=
  Formalism.IndefR.Lev.levG A β (prinDat A Z)

def prinInf (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Set (GA D A) :=
  {g | Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z)}

def NoLift (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (om : WRep A W) (m : Measure (GA D A)) (u : GA D A → ℂ) : Prop :=
  ∀ f, IsThetaFunO ψ A W f → ∀ h, up om m f u h = 0

def Kills (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W) (m : Measure (GA D A))
    (u : GA D A → ℂ) : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) W φ → ∀ h,
    Eis.dblInt A χ⁻¹ m (fun g => thetaKO omh g h φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0

structure Defin (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) : Prop where
  inf : IsInfFam θ
  sig : HSpace.SigOK A
  pos : HSpace.IsPosDef A
  cart : IsCartanFrame A cA
  one : ∀ τ, IsCartanInv (gramAt D A τ) 1
  cA_eq : ∀ τ, cA τ * (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) = Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 * cA τ
  maj : IsMaj A a
  maj_eq : ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * 1) * compAt θ τ a.1 = 1

structure Places (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop where
  frame : Formalism.L2.DIV.IsFrame β (frameLat A)
  idem : ∃ e : AE D, IsIdemSum e Z
  two : ∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

structure Form (θ : InfFam D) (A : HSp D) (cA : CptF A) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D))
    (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (χW : (AE D)ˣ →* Circle) (r t : ℕ) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) : Prop where
  mem : u ∈ A0 θ A cA
  fix : ∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g
  param : LFun.IsParamFun D.sp.cm.sig A.gram (frameLat A) (under Z : Set (FinPl D)) u par
  unr : LFun.UnrOff χW (under Z : Set (FinPl D))
  str : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under Z : Set (FinPl D)) r t c par (LFun.val (F := D.host.F) χW) (LFun.val (F := D.host.F) χW)

structure Occ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {A W : HSp D} (sW : RealMat W) (om : WRep A W) (m : Measure (GA D A))
    (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (u : GA D A → ℂ) (Φ : WO A W → ℂ) : Prop where
  cart : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)
  fock : IsFockVec ψ θ A W (fun _ => 1) sW Φ
  sph : IsSphOff ψ A W (frameLat A) (frameLat W) (under Z) Φ
  fix : ∀ κ ∈ prin A β Z, om (κ, 1) Φ = Φ
  real : ∀ ν 𝓕, IsCovolOne (ratL W A) ν 𝓕 → ∀ mR : Measure (GinfC A), mR.IsHaarMeasure →
    ∫ b : GinfC A, wcoef om ν 𝓕 Φ Φ b * rcoef m u u b ∂mR ≠ 0

def DownNe (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A W : HSp D) (t : ℕ) (χA χW : (AE D)ˣ →* Circle) (om : WRep A W)
    (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E))
    (m : Measure (GA D A)) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) (sW : RealMat W) (Φ : WO A W → ℂ),
    Defin θ A cA a → HSpace.SigOK W → 0 < W.rank → A.rank = W.rank + t → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) →
    IsWeilDatumO ψ A W χA χW om → Places A β Z → m.IsHaarMeasure → Form θ A cA β Z χW W.rank t u par →
    Occ ψ θ sW om m β Z u Φ → ¬ NoLift ψ om m u

end GlobalTheory.Core.Rk.Exh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
section
noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions

def HtRowsS {D : D7} (L : SizeData₂ D) (CY : ℝ) : Prop :=
  Nonempty (ParameterChoice' D L) ∧
  (Real.log D.host.rdE ≤ L.sc.L ∧ |L.logDerivativeAtOne| ≤ L.sc.L ∧ Real.log (4 * L.sc.x) ≤ L.sc.L) ∧
  (∀ i, Real.log (D.host.g i) ≤ CY * L.sc.L + 1) ∧
  (4 * (D.R.N D.R.m : ℝ) ^ 3 ≤ L.etaSz ∧ (D.R.t : ℝ) ≤ L.etaSz ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧ (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b') ∧
  DelNat D ∧ ThickUp L

end GlobalTheory.CoreHt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
section
noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SiegelWeilFock (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank →
    (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

end GlobalTheory.Core.Rk.IP

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section OfTower

variable (W : GlobalTheory.Core.Rk.Tower D)

def comOf : Com D := ⟨W.θ, W.ψ, W.toLevCh.mu (), W.eta, W.Pg, W.triv, W.chi⟩

def stageY (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), W.MY j, W.ΛY j, W.βY j, W.datYt () j W.triv, W.νY j, W.fdY j⟩

def stageX : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, W.MX, W.ΛX, W.βX, W.datXt (), W.νX, W.fdX⟩

def stepY (k : ℕ) : Step (comOf W) (stageY W k) (stageY W (k + 1)) := ⟨W.ωY k, W.vY k, W.ItY k, W.ioY k⟩

def stepX : Step (comOf W) (stageY W (D.R.m - 1)) (stageX W) := ⟨W.ωX, W.vX, W.ItX, W.ioX⟩

end OfTower

def PiLocalization₂.InFlag (s : PiLocalization₂ D) (κ : GA D s.V) : Prop :=
  κ ∈ GfC s.V ∧ Lev.finE s.V κ ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β s.L

def SameBlock (s s' : PiLocalization₂ D) (κ : GA D s.V) (κ' : GA D s'.V) : Prop :=
  HEq (Formalism.L2.DIV.rTup s.β s.L (Lev.finE s.V κ)) (Formalism.L2.DIV.rTup s'.β s'.L (Lev.finE s'.V κ'))

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.FinZeta (Gv embV VacFin)
open GlobalTheory.AdelicU (frameLat)

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TransferOn (D : D7) (C : HeightOneSpectrum (𝓞 D.host.F) → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t →
  ∀ v, C v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χS w' ∧ GlobalTheory.LFun.UnrAt χT w') →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (U : Submodule ℂ (WO S T → ℂ))
    (hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U) (f : U), VacFin ψ S T v f →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv S v) X) (x : X) (B : Multiset ℂˣ),
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ x B →
  ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (Gv T v) X') (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ a a' (u : U) y, b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a y) = ρ' a' (b u y)) → b f x ≠ 0 →
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig T.gram (frameLat T) h ρ' (b f x) (stepPar χS χT t (fun _ => B) w)

def CosetSym {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∀ g : G, Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)} = Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g⁻¹ : G) : G ⧸ K)}

end GlobalTheory.ChainOnto

end
end

