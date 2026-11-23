module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

open GlobalTheory.Grid

variable {D : D7}

def InId (I : Ideal (𝓞 D.host.E)) (z : Lev.EAf D) : Prop :=
  ∃ h : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, (⟨z, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I

def IsUnitDet (e : AE D) {k : ℕ} (N : Matrix (Fin k) (Fin k) (Lev.EAf D)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = 1 - toEAf D e + toEAf D e * N.det ∧
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E


open Classical in
def unitChar (ν : (AE D)ˣ →* Circle) (e : AE D) {k : ℕ} (N : Matrix (Fin k) (Fin k) (Lev.EAf D)) : ℂ :=
  if h : ∃ x, IsUnitDet e N x then (((ν h.choose)⁻¹ : Circle) : ℂ) else 0

def rightBlock {κ : Type} [Zero κ] {k d : ℕ} (a : ℕ) (Y : Matrix (Fin k) (Fin d) κ) : Matrix (Fin k) (Fin k) κ :=
  fun i j => if h : a + j.1 < d then Y i ⟨a + j.1, h⟩ else 0


open Classical in
def stdFst (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (βA : GL (Fin A.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A WW) : ℂ :=
  if IsHalf e x ∧ IsIntM (frMapO A WW βA βW x) ∧ ∀ i j, A.rank ≤ i.1 → InId I (frMapO A WW βA βW x i j) then
    unitChar ν e (topL A.rank (frMapO A WW βA βW x))
  else 0

def dualCoord (A' WW : HSp D) (βA' : GL (Fin A'.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (y : WO A' WW) :
    Matrix (Fin A'.rank) (Fin WW.rank) (Lev.EAf D) :=
  eToEAf D D.host.xi0 • frMapAdj A' WW βA' βW y


open Classical in
def stdSnd (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D)
    (βA' : GL (Fin A'.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (y : WO A' WW) : ℂ :=
  if IsHalf (cA D e) y ∧ IsIntM (dualCoord A' WW βA' βW y) ∧ ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW y i j) then
    unitChar ν e (rightBlock a (dualCoord A' WW βA' βW y))
  else 0

structure Rig (V : HSp D) where

  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  β : GL (Fin V.rank) (Lev.EAf D)

  s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

  B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

def Rig.Is {V : HSp D} (r : Rig V) : Prop :=
  IsSelfDualC V r.Λ ∧ Formalism.L2.DIV.IsFrame r.β r.Λ ∧
    ∀ τ, IsCartanInv (gramAt D V τ) (r.s τ) ∧ ∃ p, IsONBasis (gramAt D V τ) (r.s τ) (r.B τ) p

def Rig.IsStd {V : HSp D} (r : Rig V) : Prop :=
  V.gram = 1 ∧ (∀ y, y ∈ r.Λ ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) ∧ ∀ τ, r.s τ = 1 ∧ r.B τ = 1


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Tri (T : Type) (A A' WW : HSp D) where

  rA : Rig A

  rA' : Rig A'

  rW : Rig WW

  ω : T → WRep A WW

  ω' : T → WRep A' WW

  vac : WO A WW → ℂ

  vac' : WO A' WW → ℂ

  e : T → AE D

  c : T → Pl D.host.E → ℕ

  f : T → WO A WW → ℂ

  f' : T → WO A' WW → ℂ

  m : Measure (GA D A)

  fd : Set (GA D A)

  m' : Measure (GA D A')

  fd' : Set (GA D A')

namespace Tri

variable {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

def ideal (S : T → Finset (Pl D.host.E)) (t : T) : Ideal (𝓞 D.host.E) := ∏ w ∈ S t, w.asIdeal ^ X.c t w

structure Is (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (Pl D.host.E)) : Prop where

  rank : A.rank + A'.rank = WW.rank

  rigA : X.rA.Is

  rigA' : X.rA'.Is

  rigW : X.rW.Is

  weil : ∀ t, IsWeil ψ true A WW (β t) (β t / α t) (X.ω t)

  weil' : ∀ t, IsWeil ψ false A' WW (α t) (α t / β t) (X.ω' t)

  isVac : IsVacO ψ θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac

  isVac' : IsVacO ψ θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac'

  idem : ∀ t, IsIdemSum (X.e t) (S t)

  expo : ∀ t, ∀ w ∈ S t, GlobalTheory.CMVal.ExpAt (νH t) w (X.c t w)

  fst : ∀ t, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) (X.e t) (latO (neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 X.vac
    (stdFst (α t / β t) (X.e t) (X.ideal S t) A WW X.rA.β X.rW.β) (X.f t)

  snd : ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D (X.e t)) (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 X.vac'
    (stdSnd (α t / β t) (X.e t) (X.ideal S t) A.rank A' WW X.rA'.β X.rW.β) (X.f' t)

  meas : X.m.IsHaarMeasure ∧ IsFundamentalDomain (GQ A) X.fd X.m

  meas' : X.m'.IsHaarMeasure ∧ IsFundamentalDomain (GQ A') X.fd' X.m'

def ker (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) : ℂ :=
  thetaKO (X.ω t) g h (pureTensorO ψ θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P)

def ker' (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) (g : GA D A') : ℂ :=
  thetaKO (X.ω' t) g h (pureTensorO ψ θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P)

def I (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) : ℂ := ∫ g in X.fd, X.ker ψ θ t P h g ∂X.m

def I' (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) : ℂ := ∫ g in X.fd', X.ker' ψ θ t P h g ∂X.m'

def IsConst (c : T → ℂ) : Prop :=
  (∃ t, c t ≠ 0) ∧ ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank), ∀ t,
    (∀ h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m ∧ IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧
    (∃ h, X.I' ψ θ t P' h ≠ 0) ∧ ∀ h, X.I ψ θ t P h = c t * X.I' ψ θ t P' h

def RationalSums {L : Type} [Field L] (σ : L →+* ℂ) : Prop :=
  ∃ Ω Ω' : ℂ, Ω ≠ 0 ∧ Ω' ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW,
    (∀ k, IntegrableOn (X.ker ψ θ t (MvPolynomial.monomial k 1) h) X.fd X.m ∧
      ∃ z : L, X.I ψ θ t (MvPolynomial.monomial k 1) h = Ω * σ z) ∧
    ∀ k, IntegrableOn (X.ker' ψ θ t (MvPolynomial.monomial k 1) h) X.fd' X.m' ∧
      ∃ z : L, X.I' ψ θ t (MvPolynomial.monomial k 1) h = Ω' * σ z

end Tri

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks} (G : GridPre R)

def alpha (R : RealDat D Fam Ks) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  R.toLevCh.mu t (j.1 + 1) * R.eta ^ (rkV D i j % 2)

def beta (i j : Fin D.R.m) (_ : T) : (AE D)ˣ →* Circle := G.chi (D.R.m - i) * R.eta ^ (rkV D i j % 2)

def nuH (i j : Fin D.R.m) (t : T) : Formalism.L2.Host.HChar D.host.E := R.C.mu0 j * R.xiH t / G.chiH (D.R.m - i)


open Classical in
def places (t : T) : Finset (Pl D.host.E) := G.toPlaceDat.W R.Pg ∪ R.Q t

def IsSum (N₁ N₂ : Node D) (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)) : Prop :=
  N₁.V.rank + N₂.V.rank = WW.rank ∧
    ∃ (ι₁ : N₁.V.V →ₗ[D.host.E] WW.V) (ι₂ : N₂.V.V →ₗ[D.host.E] WW.V),
      Formalism.BasicNotions.HSpace.IsIsomEmb N₁.V WW ι₁ ∧ Formalism.BasicNotions.HSpace.IsIsomEmb N₂.V WW ι₂ ∧ (∀ x y, WW.hD (ι₁ x) (ι₂ y) = 0) ∧
      ∀ z : WW.V, WW.frame.equivFun z ∈ Λ ↔ ∃ x y, N₁.InLat x ∧ N₂.InLat y ∧ z = ι₁ x + ι₂ y

def BottomInField (i j : Fin D.R.m) : Prop :=
  ∃ (A A' WW : HSp D) (X : Tri T A A' WW),
    A.rank + 2 * ((D.R.m - (j + 1)) / 2) = rkV D (i + 1) (j + 1) ∧ A'.rank + 2 * ((D.R.m - j) / 2) = rkV D i j ∧
    X.rA.IsStd ∧ X.rA'.IsStd ∧ X.rW.IsStd ∧ X.Is R.ψ R.θ (alpha R i j) (beta G i j) (nuH G i j) (places G) ∧
    X.RationalSums R.ψ R.θ D.what₂.embLL

def LRatiosInField (i j : Fin D.R.m) : Prop :=
  ∀ (t : T) (L L₀ : ℂ → ℂ), GlobalTheory.CMVal.IsHeckeL (nuH G i j t) L → GlobalTheory.CMVal.IsHeckeL (nuH G i j Fam.μ0) L₀ →
    ∀ s : ℕ, 1 ≤ s → s ≤ bigN D + 1 → ∃ ρ : D.what₂.LL, L s = D.what₂.embLL ρ * L₀ s

structure FieldCond : Prop where

  base : Formalism.L2.Host.ValLL D R.C

  aux : G.ValuesInField

  twist : ∀ t, (R.xiH t).ValuesIn 0 D.what₂.embLL

  ratios : ∀ i j, LRatiosInField G i j

  bottom : ∀ i j, BottomInField G i j

end GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

end
