module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.Chain (IsVacVec ptOf signed)
open GlobalTheory.ChainOnto (stepPar)

namespace GlobalTheory.EvenOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UpPair (t : ℕ) (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ al be ga de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |e|) ∧
    S = dualPar (signed (al ++ be) (ga ++ de) aT) ∧ S' = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)

structure Com (D : D7) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  S : Finset (HeightOneSpectrum (𝓞 D.host.F))
  n : ℕ
  t : ℕ
  m : ℕ
  χ : ℕ → ((AE D)ˣ →* Circle)
  a : ℕ → D.what₂.Tau → ℚ

structure Com.Is (c : Com D) : Prop where
  inf : IsInfFam c.θ
  std : IsStdChar D c.ψ (-1)
  hecke : ∀ k < c.m, IsHeckeChar D (c.χ k) ∧ Formalism.L2.Theta.ResEta D (c.χ k) 0
  exp : ∀ k < c.m, ∀ τ, HasInfExp D (c.χ k) τ (c.a k τ)
  unr : ∀ k < c.m, GlobalTheory.LFun.UnrOff (c.χ k) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  ne : ∀ i k, i < k → k < c.m → ∀ τ, c.a i τ ≠ c.a k τ
  one_le : 1 ≤ c.n
  step : c.n + 2 ≤ c.t

structure PiLocalization₂ (D : D7) where
  V : HSp D
  par : D.what₂.Tau → SPar
  M : DSModel V par
  J : Subgroup (GA D V)
  ν : Measure (GA D V)
  fd : Set (GA D V)

abbrev PiLocalization₂.Λ (s : PiLocalization₂ D) : Submodule (𝓞 D.host.E) (Fin s.V.rank → D.host.E) := GlobalTheory.AdelicU.frameLat s.V

def intOff (c : Com D) (s : PiLocalization₂ D) : Set (GA D s.V) :=
  {g | ∀ v ∉ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v}

def PiLocalization₂.big (s : PiLocalization₂ D) : Set (GA D s.V) := {g | ∃ b : GinfC s.V, ∃ κ ∈ s.J, g = (b : GA D s.V) * κ}

structure PiLocalization₂.Is (c : Com D) (j : ℕ) (s : PiLocalization₂ D) : Prop where
  rank : s.V.rank = c.n + j * c.t
  sigOK : s.V.SigOK
  witt : GlobalTheory.Cusp.wittIndex s.V < c.t
  selfDual : IsSelfDualC s.V s.Λ
  fin : s.J ≤ GfC s.V
  isOpen : ∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J
  stab : ∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v
  off : ∀ k ∈ GfC s.V, k ∈ intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J
  sph : SphOff (s.J : Set (GA D s.V)) 1 c.S
  split : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J,
    ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂
  haar : s.ν.IsHaarMeasure
  fund : IsFundamentalDomain (GQ s.V) s.fd s.ν

abbrev PiLocalization₂.CC (c : Com D) (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := MultT c.θ s.M (s.J : Set (GA D s.V)) 1

abbrev PiLocalization₂.val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) : GA D s.V → ℂ :=
  (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v

def PiLocalization₂.KF (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M) :=
  Submodule.span ℂ {w | ∃ v : s.M.Vec, (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ w = PiTensorProduct.tprod ℂ v}

abbrev PiLocalization₂.pet (s : PiLocalization₂ D) (f₁ f₂ : GA D s.V → ℂ) : ℂ := Lift.pet s.ν s.fd f₁ f₂

variable {c : Com D} {s s' : PiLocalization₂ D}

def coefW (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)) (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (Φ : WO s.V s'.V → ℂ) (g : GA D s.V) : ℂ := ∫ w in X, ω (g, 1) Φ w * conj (Φ w) ∂m

structure PreStep (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ))
    (f : WO s.V s'.V → ℂ) : Prop where
  weil : IsWeilDatumO c.ψ s.V s'.V (c.χ k) (c.χ k) ω
  par : ∀ τ, UpPair c.t (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ)
  vac : IsVacVec c.ψ c.θ s.M s'.M f
  sph : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S f
  law : ∀ φ, ∀ κ ∈ s.J, ∀ κ' ∈ s'.J, ω (κ, κ') (ptOf c.ψ c.θ s.M s'.M f φ) = ptOf c.ψ c.θ s.M s'.M f φ
  supp : ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ φ, ∀ g ∈ intOff c s, g ∉ s.big →
    coefW ω m X (ptOf c.ψ c.θ s.M s'.M f φ) g = 0

structure Step (c : Com D) (s s' : PiLocalization₂ D) where
  ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)
  f : WO s.V s'.V → ℂ
  It : PolF D s'.V.rank s.V.rank →ₗ[ℂ] SmT s'.M →ₗ[ℂ] SmT s.M
  io : s'.CC c →ₗ[ℂ] s.CC c

def Step.pt (p : Step c s s') : PolF D s'.V.rank s.V.rank → (WO s.V s'.V → ℂ) := ptOf c.ψ c.θ s.M s'.M p.f

structure Step.Is (k : ℕ) (p : Step c s s') : Prop where
  pre : PreStep c k s s' p.ω p.f
  it : IsItW c.θ s.M s'.M p.ω p.pt p.It
  io : Lift.IsIo s'.ν s'.fd (thetaKO p.ω) p.pt p.It (s'.CC c) (s.CC c) p.io

inductive Reach (c : Com D) (s₀ : PiLocalization₂ D) : ℕ → ∀ s : PiLocalization₂ D, (s.CC c →ₗ[ℂ] s₀.CC c) → Prop
  | zero : Reach c s₀ 0 s₀ LinearMap.id
  | step {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (h : Reach c s₀ k s Θ) {s' : PiLocalization₂ D} (hs' : s'.Is c (k + 1))
      (p : Step c s s') (hp : p.Is k) : Reach c s₀ (k + 1) s' (Θ ∘ₗ p.io)

def OntoAll (D : D7) : Prop :=
  ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ c.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → Function.Surjective Θ

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

def chainPar (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) : GlobalTheory.LFun.Fam D.host.E :=
  Nat.rec B (fun i B' => stepPar (c.χ i) (c.χ i) c.t B') k

def LNe (c : Com D) (χ : (AE D)ˣ →* Circle) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  ∃ l : ℂ, l ≠ 0 ∧ GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B χ (z + 1 / 2)) ((c.t : ℂ) / 2) l

def Step.up (p : Step c s s') (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : GA D s'.V → ℂ :=
  fun h => ∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * F g ∂s.ν

def hgtS (c : Com D) (s : PiLocalization₂ D) (a : GL (Fin s.V.rank) (AE D)) (g : GA D s.V) : ℝ :=
  (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w g)) *
    ∏ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g)

def Step.zint (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (g : GA D s.V) : ℂ := coefW p.ω m X (p.pt φ) g * conj (s.pet (rTr s.V g F) F)

def ForStage (D : D7) (Φ : ∀ (_ : Com D) (_ : ℕ) (_ : PiLocalization₂ D), Prop) : Prop :=
  ∀ c : Com D, c.Is → ∀ j ≤ c.m, ∀ s : PiLocalization₂ D, s.Is c j → Φ c j s

def FinDim (D : D7) : Prop := ForStage D fun c _ s => FiniteDimensional ℂ (s.CC c)

def MetEx (D : D7) : Prop := ForStage D fun c _ s => ∃ ipD ip, IsMet c s ipD ip

def EigSpan (D : D7) : Prop := ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ B, IsPar u B} = ⊤

def ParBound (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank (((s.V.rank : ℝ) - 1) / 2)

def ParOfVal (D : D7) : Prop := ForStage D fun c _ s => ∀ (x : s.CC c) w B, PiLocalization₂.val x w ≠ 0 → ParFun c s (PiLocalization₂.val x w) B → IsPar x B

def ParIndep (D : D7) : Prop := ForStage D fun c _ s => ∀ (ι : Type) (x : ι → s.CC c) (B : ι → GlobalTheory.LFun.Fam D.host.E),
  (∀ i, IsPar (x i) (B i)) →
  (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ x

def ForStep (D : D7) (Φ : ∀ (c : Com D) (_ : ℕ) (s s' : PiLocalization₂ D) (_ : Step c s s'), Prop) : Prop :=
  ∀ c : Com D, c.Is → ∀ k < c.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) → ∀ p : Step c s s', p.Is k → Φ c k s s' p

def StepEx (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ k < c.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) →
  ∀ ω f, PreStep c k s s' ω f → ∃ p : Step c s s', p.ω = ω ∧ p.f = f ∧ p.Is k

def UpSpan (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) φ, ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ∈ Submodule.span ℂ {F | ∃ (y : s'.CC c), ∃ w ∈ s'.KF, F = PiLocalization₂.val y w}

def UpAdj (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ (u : s.CC c) (y : s'.CC c) φ, ∀ v ∈ s.KF, ∀ w ∈ s'.KF,
  s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = s.pet (PiLocalization₂.val (p.io y) (p.It φ w)) (PiLocalization₂.val u v)

def UpPar (D : D7) : Prop := ForStep D fun c k s s' p => ∀ (u : s.CC c) B φ, IsPar u B → ∀ v ∈ s.KF,
  p.up φ (PiLocalization₂.val u v) ≠ 0 → ParFun c s' (p.up φ (PiLocalization₂.val u v)) (stepPar (c.χ k) (c.χ k) c.t B)

def ZetaNe (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v ∈ s.KF,
  ∀ u : s.CC c, u ≠ 0 → (∫ g in intOff c s, p.zint m X φ (PiLocalization₂.val u v) g ∂s.ν) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (c.t : ℝ) / 2 ∧
        IntegrableOn (fun g => p.zint m X φ (PiLocalization₂.val u v) g * (hgtS c s a g : ℂ) ^ ((s₁ : ℂ) - (c.t : ℂ) / 2)) (intOff c s) s.ν

def RealZeta (D : D7) : Prop := ForStep D fun c _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∃ φ, ∃ v : s.M.Vec,
  (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ ∀ mR : Measure (GinfC s.V), mR.IsHaarMeasure →
    let z : GinfC s.V → ℂ := fun g => coefW p.ω m X (p.pt φ) g *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)
    (∫ g, z g ∂mR) ≠ 0 ∧
    ∀ a : GL (Fin s.V.rank) (AE D), GlobalTheory.Doubling.IsMaj s.V a →
      (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) →
      ∃ s₁ : ℝ, s₁ < (c.t : ℝ) / 2 ∧ Integrable (fun g : GinfC s.V => z g *
        ((∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) : ℝ) : ℂ) ^
          ((s₁ : ℂ) - (c.t : ℂ) / 2)) mR

def UpNe (D : D7) : Prop := ForStep D fun c k s _ p => ∀ (u : s.CC c) B, IsPar u B → LNe c (c.χ k) B →
  ∃ φ, ∃ v ∈ s.KF, p.up φ (PiLocalization₂.val u v) ≠ 0

def StepUp (D : D7) : Prop := ForStep D fun c k s s' p => ∀ ipD ip ipD' ip', IsMet c s ipD ip → IsMet c s' ipD' ip' →
  ∀ (u : s.CC c) B, IsPar u B → LNe c (c.χ k) B →
    ∃ x : s'.CC c, (∀ y, ip' y x = ip (p.io y) u) ∧ IsPar x (stepPar (c.χ k) (c.χ k) c.t B)

def ChainL (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B c.n (((c.n : ℝ) - 1) / 2) →
  ∀ k < c.m, LNe c (c.χ k) (chainPar c B k)

def ChainUp (D : D7) : Prop :=
  ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ c.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → s.Is c k ∧
      ∀ ipD₀ ip₀ ipD ip, IsMet c s₀ ipD₀ ip₀ → IsMet c s ipD ip → ∀ (u : s₀.CC c) B, IsPar u B →
        ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k)

theorem chainPar_succ (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B (k + 1) = stepPar (c.χ k) (c.χ k) c.t (chainPar c B k) := rfl

end GlobalTheory.EvenOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def KF {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Submodule ℂ (SmT M) :=
  Submodule.span ℂ {w | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}


variable (L) in
def levRow : Subgroup (GA D (Yc D 0)) :=
  Lev.levA (Yc D 0) (congLev D.sp.cm (Yc D 0).gram (L.ΛY 0) (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}))


variable (L) in
abbrev Rows (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (Yc D 0) S) : Submodule ℂ (SmT M →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) :=
  MultT θ M (levRow L : Set _) 1

variable (G : GridData L sc)

def lev (X : Node) : Subgroup (GA D (G.V X)) := Lev.levA (G.V X) (G.levCong X)

abbrev CoreForms (θ : InfFam D) (i : ℕ) {S : D.what₂.Tau → SPar} (M : DSModel (G.V (.core i)) S) :
    Submodule ℂ (SmT M →ₗ[ℂ] (GA D (G.V (.core i)) → ℂ)) :=
  MultT θ M (lev G (.core i) : Set _) 1

def depLat (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) where
  carrier := {u | u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) (fun _ => True) ∧
    ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.latS p) (G.latT p))}
  zero_mem' := ⟨zero_mem _, fun e _ => by rw [smul_zero]; exact zero_mem _⟩
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun e he => by rw [smul_add]; exact add_mem (ha.2 e he) (hb.2 e he)⟩
  neg_mem' := fun ha => ⟨neg_mem ha.1, fun e he => by rw [smul_neg]; exact neg_mem (ha.2 e he)⟩

variable {G} (W : G.Weil)

def Dep (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : Prop :=
  IsThetaFunO W.ψ (G.pS p) (G.pT p) f ∧ IsLatVac (heisO W.ψ (G.pS p) (G.pT p)) (depLat G p) f

def part (M : Vol G) (ρ : G.RealVec) (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) (n : ℕ) (h : n ≤ D.R.m) : Fn G (.grid n 0) :=
  liftP W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) u

theorem part_m (M : Vol G) (ρ : G.RealVec) (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) :
    part W M ρ Φ u D.R.m le_rfl = thetaChi W M ρ Φ u := rfl

def RapidRow (M : Vol G) (u : GA D (Yc D 0) → ℂ) : Prop :=
  ∀ ρ Φ n h, RapidDec (G.V (.grid n 0)) (part W M ρ Φ u n h)


variable (G) in
abbrev CoreVol : Type := ∀ i, GlobalTheory.Unf.Vol (G.V (.core i))

def dn (v : CoreVol G) (i : ℕ) (f : Sch G (.coreDown i)) (F : Fn G (.core (i + 1))) : Fn G (.core i) :=
  fun g => ∫ h in (v (i + 1)).𝓕, W.kerA (.coreDown i) f h g * F h ∂(v (i + 1)).μ

def IsColChain (v : CoreVol G) (Ψ : ∀ i, Fn G (.core i)) : Prop :=
  (∀ i, i ≤ D.R.m → RapidDec (G.V (.core i)) (Ψ i)) ∧
    ∀ i, i < D.R.m → ∃ f : Sch G (.coreDown i), Dep W (.core i) f ∧ Ψ i = dn W v i f (Ψ (i + 1))

def Reach (v : CoreVol G) : Set (Fn G (.core 0)) :=
  {F | ∃ Ψ : ∀ i, Fn G (.core i), IsColChain W v Ψ ∧ Ψ 0 = F ∧
    ∃ c ∈ Cols G W.θ, ∃ ξ : Module.Dual ℂ (coefPlus G W.θ).W, Ψ D.R.m = pairVec (coefPlus G W.θ) ξ c}


variable (G) in
def per0 (M : Vol G) (F : Fn G (.core 0)) (u : GA D (Yc D 0) → ℂ) : ℂ :=
  ∫ h in M.fd (.grid 0 0), F (stabilizerEmbedding G.sp.dec0 h) * u h ∂M.ν (.grid 0 0)

abbrev GP := ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}, G.Weil → Vol G → Prop

def OffQ (D : D7) : Prop := Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)

def All (Q : GP) : Prop :=
  ∀ (D : D7), OffQ D → ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (sc : Consts) (G : GridData L sc) (W : G.Weil) (M : Vol G),
    M.IsRow → Q W M

def Gap (Q : GP) : Prop :=
  ∀ (D : D7), OffQ D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (sc : Consts), sc.cGap = 1 →
    ∀ (G : GridData L sc) (W : G.Weil) (M : Vol G), M.IsRow → Q W M

def Ev (Q : GP) : Prop :=
  ∀ ε CF : ℝ, 6510 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ →
    ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (G : GridData L ⟨1, CF, large₂.sc.b⟩) (W : G.Weil) (M : Vol G),
      M.IsRow → Q W M

def SizeGap : Prop :=
  ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D

def DepFixed : Prop := All fun {D} {T} _ _ {G} W _ => ∀ i, i < D.R.m → ∀ p : Pair T, p = .chi i 0 ∨ p = .core i →
  ∀ f, Dep W p f → ∀ k ∈ lev G p.small, ∀ k' ∈ lev G p.big, W.om p (G.toPair p k k') f = f

def DatumDep : Prop := All fun {_} _ _ _ _ W _ => ∀ ρ Φ i, Dep W (.chi i.1 0) (W.datum ρ Φ i)

def CoreModels : Prop := All fun {D} _ _ {sc} {G} W _ => ∀ i, i ≤ D.R.m →
  ∃ MP : DSModel (G.V (.core i)) (Node.par D sc.cGap (.core i)), cart MP = W.cart (.core i)

def RowRapid : Prop := Gap fun {D} _ {L} _ _ W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, ∀ w, RapidRow W M (t w) ∧ ∀ ρ Φ, ThetaConv W M ρ Φ (t w)

def PeriodNe : Prop := Ev fun {D} _ {L} {sc} {G} W M => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∀ t ∈ Rows L W.θ M₀, t ≠ 0 → ∀ w : SmT M₀, w ≠ 0 →
    ∃ y ∈ CoreForms G W.θ 0 MP, ∃ v ∈ KF MP, per0 G M (y v) (t w) ≠ 0

def CoreOnto : Prop := Gap fun {D} _ _ {sc} {G} W _ => ∀ (v : CoreVol G)
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), cart MP = W.cart (.core 0) →
    ∀ y ∈ CoreForms G W.θ 0 MP, ∀ x ∈ KF MP, y x ∈ Submodule.span ℂ (Reach W v)

def Ascent : Prop := All fun {D} _ _ _ {G} W M => ∀ (v : CoreVol G) (Ψ : ∀ i, Fn G (.core i)), IsColChain W v Ψ →
  ∀ u, RapidRow W M u → per0 G M (Ψ 0) u ≠ 0 → ∃ ρ Φ, Bplus W M (Ψ D.R.m) (thetaChi W M ρ Φ u) ≠ 0

def WeakSep : Prop := Ev fun {D} _ {L} _ {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, t ≠ 0 → ∀ w : SmT M₀, w ≠ 0 → ∃ ρ ξ, ∃ Ψ ∈ Cols G W.θ, ∃ Φ, fPsiPhi W M ρ ξ Ψ Φ (t w) ≠ 0

theorem offQ_of_sizeRows {large₂ : SizeData₂ D} (h : SizeRows large₂) : OffQ D := by
  obtain ⟨⟨Pm, -, -⟩, -⟩ := h
  exact ⟨UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host D.host.pde_prime (Pm.level_split _ D.host.pde_level.1),
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host D.host.pde'_prime (Pm.level_split _ D.host.pde_level.2)⟩

theorem dep_vac (i : ℕ) (h : i < D.R.m) : Dep W (.chi i 0) (W.vac i) :=
  ⟨(W.vac_is i h).2.theta, fun u hu => (W.vac_is i h).2.lat.1 u hu.1, fun e he u hu => (W.vac_is i h).2.lat.2 e he u hu.1⟩

end GlobalTheory.SepRows

end
end

