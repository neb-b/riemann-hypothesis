module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Formalism.LocalRingCardinality.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Com (D : D7) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  μ : ℕ → ((AE D)ˣ →* Circle)
  η : (AE D)ˣ →* Circle
  Pg : Finset (Pl D.host.E)
  P : LevelP Pg D.R.r ℂ
  chi : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ


open Classical in
def Com.S (c : Com D) : Finset (HeightOneSpectrum (𝓞 D.host.F)) := c.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def Com.chS (c : Com D) (j : ℕ) : (AE D)ˣ →* Circle := (Lift.chrStep c.μ c.η j).1

def Com.chT (c : Com D) (j : ℕ) : (AE D)ˣ →* Circle := (Lift.chrStep c.μ c.η j).2

structure Com.Is (c : Com D) : Prop where
  inf : IsInfFam c.θ
  std : IsStdChar D c.ψ (-1)
  chars : Lift.CharsOK c.μ c.η D.R.m
  exp : ∀ (j : Fin D.R.m) (τ : D.what₂.Tau), HasInfExp D (c.μ ((j : ℕ) + 1)) τ (-(D.hc τ).e j)
  unr : ∀ j : Fin D.R.m, GlobalTheory.LFun.UnrOff (c.μ ((j : ℕ) + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  res : ∀ j : Fin D.R.m, ∃ H : Formalism.L2.Host.HChar D.host.E, ChrEq (c.μ ((j : ℕ) + 1)) H ∧
    ∀ PP ∈ c.Pg, IsRes H PP (c.chi ((j : ℕ) + 1) PP)⁻¹
  split : ∃ e : AE D, IsIdemSum e c.Pg

structure PiLocalization₂ (D : D7) where
  V : HSp D
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

structure PiLocalization₂.Is (c : Com D) (j : ℕ) (s : PiLocalization₂ D) : Prop where
  rank : s.V.rank = D.R.rankY j
  sigOK : s.V.SigOK
  sig : ∀ τ : D.host.E →+* ℂ, s.V.sig τ = sigYD D.R j
  par : s.par = parB (Ptw D) j
  selfDual : IsSelfDualC s.V s.Λ
  frame : Formalism.L2.DIV.IsFrame s.β s.Λ
  base : ∃ N : ℕ, Lev.IsBaseFrame s.V s.β s.Λ N ∧
    ∀ P : Pl D.host.E, P.under (𝓞 D.host.F) ∉ c.S → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
  lev : ∃ hr ξ, s.L = Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi ξ Lev.Frm.B
  haar : s.ν.IsHaarMeasure
  fund : IsFundamentalDomain (GQ s.V) s.fd s.ν

abbrev PiLocalization₂.CC (c : Com D) (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) :=
  MultT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)

abbrev PiLocalization₂.val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) : GA D s.V → ℂ :=
  (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v

def PiLocalization₂.KF (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M) :=
  Submodule.span ℂ {w | ∃ v : s.M.Vec, (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ w = PiTensorProduct.tprod ℂ v}

abbrev PiLocalization₂.pet (s : PiLocalization₂ D) (f₁ f₂ : GA D s.V → ℂ) : ℂ := Lift.pet s.ν s.fd f₁ f₂

structure Step (c : Com D) (s s' : PiLocalization₂ D) where
  ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)
  f : WO s.V s'.V → ℂ
  It : PolF D s'.V.rank s.V.rank →ₗ[ℂ] SmT s'.M →ₗ[ℂ] SmT s.M
  io : s'.CC c →ₗ[ℂ] s.CC c

variable {c : Com D} {s s' : PiLocalization₂ D}

def Step.pt (p : Step c s s') : PolF D s'.V.rank s.V.rank → (WO s.V s'.V → ℂ) :=
  pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f

structure Step.Is (j : ℕ) (p : Step c s s') : Prop where
  weil : IsWeilDatumO c.ψ s.V s'.V (c.chS j) (c.chT j) p.ω
  vec : ∃ ξ f₀, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi j) ∅ ξ f₀ p.f
  theta : ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ)
  it : IsItW c.θ s.M s'.M p.ω p.pt p.It
  io : Lift.IsIo s'.ν s'.fd (thetaKO p.ω) p.pt p.It (s'.CC c) (s.CC c) p.io

inductive Reach (c : Com D) (s₀ : PiLocalization₂ D) : ℕ → ∀ s : PiLocalization₂ D, (s.CC c →ₗ[ℂ] s₀.CC c) → Prop
  | zero : Reach c s₀ 0 s₀ LinearMap.id
  | step {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (h : Reach c s₀ k s Θ) {s' : PiLocalization₂ D} (hs' : s'.Is c (k + 1))
      (p : Step c s s') (hp : p.Is (k + 1)) : Reach c s₀ (k + 1) s' (Θ ∘ₗ p.io)

def OntoAll (D : D7) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ D.R.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → Function.Surjective Θ

structure IsMet (c : Com D) (s : PiLocalization₂ D) (ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ) (ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ) : Prop where
  pure : ∀ v v' : s.M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : s.M.H τ), (v τ : s.M.H τ)⟫_ℂ
  hermD : ∀ w w', ipD w w' = conj (ipD w' w)
  posD : ∀ w, w ≠ 0 → 0 < (ipD w w).re
  herm : ∀ x y, ip x y = conj (ip y x)
  pos : ∀ x, x ≠ 0 → 0 < (ip x x).re
  integ : ∀ (x y : s.CC c) w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν
  schur : Lift.IsSchur s.ν s.fd ipD (s.CC c) ip

def ParFun (c : Com D) (s : PiLocalization₂ D) (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) (fun g => conj (f g)) B

def IsPar (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E) : Prop := u ≠ 0 ∧ ∀ v, PiLocalization₂.val u v ≠ 0 → ParFun c s (PiLocalization₂.val u v) B

def stepPar (χS χT : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) : GlobalTheory.LFun.Fam D.host.E := fun w =>
  (B w).map (GlobalTheory.LFun.val (F := D.host.F) χS w * (GlobalTheory.LFun.val (F := D.host.F) χT w)⁻¹ * ·) +
    GlobalTheory.LFun.seg w (GlobalTheory.LFun.val (F := D.host.F) χS w) t

def chainPar (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) : GlobalTheory.LFun.Fam D.host.E :=
  Nat.rec B (fun i B' => stepPar (c.chS (i + 1)) (c.chT (i + 1)) D.R.t B') k

def LNe (c : Com D) (χ : (AE D)ˣ →* Circle) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  ∃ l : ℂ, l ≠ 0 ∧ GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B χ (z + 1 / 2)) ((D.R.t : ℂ) / 2) l

def Step.up (p : Step c s s') (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : GA D s'.V → ℂ :=
  fun h => ∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * F g ∂s.ν

def intOff (c : Com D) (s : PiLocalization₂ D) : Set (GA D s.V) :=
  {g | ∀ v ∉ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v}

def hgtS (c : Com D) (s : PiLocalization₂ D) (a : GL (Fin s.V.rank) (AE D)) (g : GA D s.V) : ℝ :=
  (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w g)) *
    ∏ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g)

def coefW (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)) (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (Φ : WO s.V s'.V → ℂ) (g : GA D s.V) : ℂ := ∫ w in X, ω (g, 1) Φ w * conj (Φ w) ∂m

def Step.zint (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (g : GA D s.V) : ℂ := coefW p.ω m X (p.pt φ) g * conj (s.pet (rTr s.V g F) F)

def ForStage (D : D7) (Φ : ∀ (_ : Com D) (_ : ℕ) (_ : PiLocalization₂ D), Prop) : Prop :=
  ∀ c : Com D, c.Is → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, s.Is c j → Φ c j s

def FinDim (D : D7) : Prop := ForStage D fun c _ s => FiniteDimensional ℂ (s.CC c)

def MetEx (D : D7) : Prop := ForStage D fun c _ s => ∃ ipD ip, IsMet c s ipD ip

def EigSpan (D : D7) : Prop := ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ B, IsPar u B} = ⊤

def ParBound (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank (((s.V.rank : ℝ) - 1) / 2)

def ParOfVal (D : D7) : Prop := ForStage D fun c _ s => ∀ (x : s.CC c) w B, PiLocalization₂.val x w ≠ 0 → ParFun c s (PiLocalization₂.val x w) B → IsPar x B

def ParIndep (D : D7) : Prop := ForStage D fun c _ s => ∀ (ι : Type) (x : ι → s.CC c) (B : ι → GlobalTheory.LFun.Fam D.host.E),
  (∀ i, IsPar (x i) (B i)) →
  (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ x

def LevFacts (D : D7) : Prop := ForStage D fun c _ s =>
  (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧
    ∀ k ∈ U, k ∈ GfC s.V → k ∈ levS s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1) ∧
  (∀ v ∉ c.S, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v,
    GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k ∈ Lev.levG s.V s.β s.L ∧
      Lev.levChi s.V s.β s.L (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k) = 1) ∧
  (∀ k ∈ Lev.levG s.V s.β s.L, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧
  (∀ k ∈ GfC s.V, k ∈ intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) →
    k ∈ Lev.levG s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1) ∧
  (∀ k ∈ Lev.levG s.V s.β s.L, ∀ k' ∈ Lev.levG s.V s.β s.L,
    Lev.levChi s.V s.β s.L (k * k') = Lev.levChi s.V s.β s.L k * Lev.levChi s.V s.β s.L k') ∧
  ∀ k ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L k‖ = 1

def ForStep (D : D7) (Φ : ∀ (c : Com D) (_ : ℕ) (s s' : PiLocalization₂ D) (_ : Step c s s'), Prop) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ k < D.R.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) →
    ∀ p : Step c s s', p.Is (k + 1) → Φ c k s s' p

def LevelLaw (D : D7) : Prop := ForStep D fun _ _ s s' p => ∀ φ,
  VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) (p.pt φ)

def UpSpan (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) φ, ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ∈ Submodule.span ℂ {F | ∃ (y : s'.CC c), ∃ w ∈ s'.KF, F = PiLocalization₂.val y w}

def UpAdj (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) (y : s'.CC c) φ, ∀ v ∈ s.KF, ∀ w ∈ s'.KF,
  s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = s.pet (PiLocalization₂.val (p.io y) (p.It φ w)) (PiLocalization₂.val u v)

def UpPar (D : D7) : Prop := ForStep D fun c k s s' p => ∀ (u : s.CC c) B φ, IsPar u B → ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ≠ 0 → ParFun c s' (p.up φ (PiLocalization₂.val u v)) (stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t B)

def CoefSupp (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ φ, ∀ g ∈ intOff c s,
  Lev.finE s.V g ∉ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → coefW p.ω m X (p.pt φ) g = 0

def ZetaNe (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v ∈ s.KF,
  ∀ u : s.CC c, u ≠ 0 → (∫ g in intOff c s, p.zint m X φ (PiLocalization₂.val u v) g ∂s.ν) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧
        IntegrableOn (fun g => p.zint m X φ (PiLocalization₂.val u v) g * (hgtS c s a g : ℂ) ^ ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) (intOff c s) s.ν

def RealZeta (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v : s.M.Vec,
  (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ ∀ mR : Measure (GinfC s.V), mR.IsHaarMeasure →
    let z : GinfC s.V → ℂ := fun g => coefW p.ω m X (p.pt φ) g *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)
    (∫ g, z g ∂mR) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ Integrable (fun g : GinfC s.V => z g *
        ((∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) : ℝ) : ℂ) ^
          ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) mR

def UpNe (D : D7) : Prop := ForStep D fun c k s _ p => ∀ (u : s.CC c) B, IsPar u B → LNe c (c.chT (k + 1)) B →
  ∃ φ, ∃ v ∈ s.KF, p.up φ (PiLocalization₂.val u v) ≠ 0

def StepUp (D : D7) : Prop := ForStep D fun c k s s' p => ∀ ipD ip ipD' ip', IsMet c s ipD ip → IsMet c s' ipD' ip' →
  ∀ (u : s.CC c) B, IsPar u B → LNe c (c.chT (k + 1)) B →
    ∃ x : s'.CC c, (∀ y, ip' y x = ip (p.io y) u) ∧ IsPar x (stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t B)

def ChainL (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2) →
  ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)

theorem chainPar_succ (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B (k + 1) = stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t (chainPar c B k) := rfl

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
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

variable {D : D7}

abbrev WRep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

section Objects

variable {A B : HSp D} (om : WRep A B) (m : Measure (GA D A))

def up (Φ : WO A B → ℂ) (u : GA D A → ℂ) : GA D B → ℂ :=
  fun h => ∫ q, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h Φ * u g) q ∂autMeasure A m

def UpConv (mH : Measure (GA D B)) (Φ : WO A B → ℂ) (u : GA D A → ℂ) : Prop :=
  (∀ h, Integrable (AutomorphicL2Unitary.descend (GQ A) fun g => thetaKO om g h Φ * u g) (autMeasure A m)) ∧
    MemL2Quotient (GQ B) mH (up om m Φ u)

def wcoef (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (Φ₁ Φ₂ : WO A B → ℂ) : GA D A → ℂ :=
  fun g => ip A B ν 𝓕 (om (g, 1) Φ₁) Φ₂

def rcoef (u₁ u₂ : GA D A → ℂ) : GA D A → ℂ := fun g => petersson A m (rTr A g u₁) u₂


variable (A) in
def hgtL (L : Lat A) (a : GL (Fin A.rank) (AE D)) (g : GA D A) : ℝ≥0 :=
  hgtAd D.sp.cm.sig (dblSp A).gram L a (io A (g, 1))

def integrand (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (L : Lat A) (a : GL (Fin A.rank) (AE D)) (Φ₁ Φ₂ : WO A B → ℂ)
    (u₁ u₂ : GA D A → ℂ) (s : ℂ) : GA D A → ℂ :=
  fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * npow (hgtL A L a g) (s - sZero A B) * rcoef m u₁ u₂ g


variable (A) in
def openOff (L : Lat A) (Sf : Finset (FinPl D)) : Set (GA D A) :=
  {g | ∀ v ∉ Sf, proj D.sp.cm.sig A.gram v g ∈ stabLoc D.sp.cm.sig A.gram L v}


variable (A) in
def SphFun (L : Lat A) (Sf : Finset (FinPl D)) (u : GA D A → ℂ) : Prop :=
  ∀ v ∉ Sf, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ∀ g, u (g * emb D.sp.cm.sig A.gram v k) = u g

end Objects

structure Pair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)) : Prop where

  setting : HidaSetting θ A B sA sB t cA

  maj : IsMaj A a

  maj_eq : ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1

  weil : IsWeilDatumO ψ A B χA χB om

  covol : IsCovolOne (ratL B A) ν 𝓕

structure Unram (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (LA : Lat A) (LB : Lat B)
    (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ) : Prop where

  sdA : IsSelfDualC A LA

  sdB : IsSelfDualC B LB

  two : ∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

  unr : LFun.UnrOff χB (Sf : Set (FinPl D))

  sph₁ : IsSphOff ψ A B LA LB Sf Φ₁

  sph₂ : IsSphOff ψ A B LA LB Sf Φ₂

def GlobalFormAt (A : HSp D) (L : Lat A) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA,
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    (∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s) m) ∧
    ∃ z, HolValueAt (fun s => ∫ g, integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s g ∂m) (sZero A B) z ∧
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * z

def GlobalForm (D : D7) : Prop := ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → GlobalFormAt A L

def IsSphSecAt (A : HSp D) (L : Lat A) (v : FinPl D) (μ : (AE D)ˣ →* Circle) (s : ℂ) (φ : Gv (dblSp A) v → ℂ) : Prop :=
  φ ∈ degPSFin D.sp.cm.sig (dblSp A).gram L v (charAt μ v) s ∧
    (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, φ (g * k) = φ g) ∧ φ 1 = 1

def ioAt (A : HSp D) (v : FinPl D) (y : Gv A v) : Gv (dblSp A) v := ioH _ D.sp.cm.sig (gram_hdbl A) (y, 1)

def SphFactor (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ →
    Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ s : ℂ, ∃ φ, IsSphSecAt A LA v χB⁻¹ s φ ∧
    ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → ∀ y : Gv A v,
      wcoef om ν 𝓕 Φ₁ Φ₂ (x * emb D.sp.cm.sig A.gram v y) *
          npow (hgtL A LA a (x * emb D.sp.cm.sig A.gram v y)) (s - sZero A B) =
        wcoef om ν 𝓕 Φ₁ Φ₂ x * npow (hgtL A LA a x) (s - sZero A B) * φ (ioAt A v y)

def IsSphCoef (A : HSp D) (L : Lat A) (v : FinPl D) (par : LFun.Fam D.host.E) (c : Gv A v → ℂ) : Prop :=
  (∃ C : ℝ, ∀ y, ‖c y‖ ≤ C) ∧
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (Gv A v) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ),
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
      LFun.IsParamVec D.sp.cm.sig A.gram L h ρ x (par w)) ∧
    (∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ∀ y, ℓ (ρ (k * y) x) = ℓ (ρ y x)) ∧ ∀ y, c y = ℓ (ρ y x)

def LocalZetaOn (D : D7) (C : FinPl D → Prop) : Prop :=
  ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D χ → ResEta D χ b →
  ∀ v, C v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → LFun.UnrAt χ w) →
  ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 →
  ∀ s : ℂ, (A.rank : ℝ) < s.re → ∀ φ, IsSphSecAt A L v χ⁻¹ s φ → ∀ par c, IsSphCoef A L v par c →
    Integrable (fun y => φ (ioAt A v y) * c y) μ ∧
      ∫ y, φ (ioAt A v y) * c y ∂μ =
        LFun.LvTw par (LFun.val χ) v (s + 1 / 2) / LFun.dv D.host.E A.rank b v s * c 1

def ParamBoundOn (D : D7) (C : FinPl D → Prop) : Prop :=
  ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v, C v → ∀ par c, IsSphCoef A L v par c → c 1 ≠ 0 →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → (par w).card = A.rank ∧
      ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((A.rank : ℝ) / 2)

def EulerRight (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ →
    Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
  ∀ s : ℂ, (A.rank : ℝ) + 1 < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m →
    ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m =
      LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m

def HeckeForm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

theorem integrand_sZero {A B : HSp D} (om : WRep A B) (m : Measure (GA D A)) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (L : Lat A) (a : GL (Fin A.rank) (AE D)) (Φ₁ Φ₂ : WO A B → ℂ) (u₁ u₂ : GA D A → ℂ) (g : GA D A) :
    integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ (sZero A B) g = wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g := by
  simp [integrand, GlobalTheory.Doubling.npow]

theorem one_mem_openOff (A : HSp D) (L : Lat A) (Sf : Finset (FinPl D)) : (1 : GA D A) ∈ openOff A L Sf :=
  fun v _ => by rw [map_one]; exact one_mem _

end GlobalTheory.Core.Rk.IP

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
section
noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

def DelNat (D : D7) : Prop := ∃ n : ℕ, D.s.Del = n

def ThickUp {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → wj D j τ ≤ L.sc.b + L.etaSz + 1

end GlobalTheory.CoreHt
end
end

