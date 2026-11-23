module

public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
public import Formalism.ZeroFreeRegion.Statement
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.SizeWindowBrackets.SBrDiv
public import Formalism.SizeWindowBrackets.Bundle0001
public import Formalism.SizeWindowBrackets.Bundle0002
public import Formalism.SizeWindowBrackets.Bundle0004
public import Formalism.SizeWindowBrackets.Bundle0003
public import Formalism.LogVandermondeBounds.Bundle0002
public import Mathlib

@[expose] public section

open Module NumberField Matrix IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBrDiv

structure Rows {I : Type} {m : ℕ} (F : Fam I m) where

  D : ℕ

  XE : InfinitePlace F.K → Matrix (Fin D) (Fin D) ℂ

  R : Submodule (𝓞 F.K) (Fin D → F.K)

  ψ : Module.Dual F.K (Fin D → F.K) →ₗ[F.K] F.Wd

namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)

def FoAll : ℝ :=
  ∑ j, ∑ᶠ z : HeightOneSpectrum (𝓞 F.K), lw z * (if plOf z ∈ F.S then ramE (plOf z) * F.Fj j (plOf z) else 0)

def EAll (u : I) (j : Fin m) : ℝ :=
  ∑ᶠ z : HeightOneSpectrum (𝓞 F.K), lw z * (if plOf z ∈ F.S then ramE (plOf z) * F.Ej u j (plOf z) else 0)

def sMean [Fintype I] : ℝ := WeightedMeanLemmas.sF F.du (fun u => muDef (F.b u) (F.X u) (F.N' u)) F.h

end Fam6

section Defs
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

def budgetAtPoint (H : Type) [Fintype H] (G : Glob) (m : ℕ) : ℝ :=
  (2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (G.x ^ G.ε) * G.x ^ G.ε

def NcTx (G : Glob) (T2 : Finset H) : ℝ :=
  (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))

def topPhi (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : H ↪ PhiSet (H := H) :=
  ⟨fun t => ⟨topPl t, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩, fun _ _ h => congrArg (fun z => z.1.2) h⟩

def aPhi (a : H → ℝ) : PhiSet (H := H) → ℝ := fun ρ => a ρ.1.2

end Defs

namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)

end Fam6

section DefsB
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

end DefsB

section DefsB2
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsB2

structure FamC (I : Type) (m : ℕ) where

  K : Type
  [indexKFirst : Field K]
  [indexKSecond : NumberField K]
  [indexKThird : StarRing K]
  [indexKFourth : _root_.NumberField.IsTotallyComplex K]

  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]

  Dall : ℕ

  D : ℕ

  D1 : ℕ

  V : I → Type
  [indexVFirst : ∀ i, AddCommGroup (V i)]
  [indexVSecond : ∀ i, Module K (V i)]
  [indexVThird : ∀ i, Module (𝓞 K) (V i)]
  [indexVFourth : ∀ i, IsScalarTower (𝓞 K) K (V i)]

  r : I → ℕ

  Vf : I → Type
  [indexFFirst : ∀ i, AddCommGroup (Vf i)]
  [indexFSecond : ∀ i, Module K (Vf i)]
  [indexFThird : ∀ i, Module (𝓞 K) (Vf i)]
  [indexFFourth : ∀ i, IsScalarTower (𝓞 K) K (Vf i)]

  d : I → ℕ
  b' : Basis (Fin D) K Wd
  X' : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ

  cc : Submodule (𝓞 K) Wd
  b : ∀ i, Basis (Fin (r i)) K (V i)
  X : ∀ i, InfinitePlace K → Matrix (Fin (r i)) (Fin (r i)) ℂ

  M : ∀ i, Submodule (𝓞 K) (V i)

  N0 : ∀ i, Submodule (𝓞 K) (V i)
  bf : ∀ i, Basis (Fin (d i)) K (Vf i)
  Xf : ∀ i, InfinitePlace K → Matrix (Fin (d i)) (Fin (d i)) ℂ

  Mf : ∀ i, Submodule (𝓞 K) (Vf i)

  j : ∀ i, V i →ₗ[K] Vf i

  σ : I → slopeLatticeData.FinPl K →₀ ℤ

  τ : slopeLatticeData.FinPl K →₀ ℤ

  B : ∀ i, V i →ₗ[K] Wd

  v : InfinitePlace K

  Y : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℂ

  Y' : Matrix (Fin D) (Fin D) ℂ

  Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ

  Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ

  ga : I → ℝ

  c : I → ℂ

  Vrow : Matrix (Fin Dall) (Fin Dall) ℂ

  U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ

  J : Matrix (Fin Dall) (Fin D) ℂ

  J1 : Matrix (Fin Dall) (Fin D1) ℂ

  S : Finset (slopeLatticeData.FinPl K)
  gain : Fin m → slopeLatticeData.FinPl K → ℝ
  Fj : Fin m → slopeLatticeData.FinPl K → ℝ
  Ej : I → Fin m → slopeLatticeData.FinPl K → ℝ

  iop : ℕ → ℝ

  T : I → ℕ

  h : I → ℝ

  lam : I → ℝ
  Dstar : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

attribute [instance] FamC.indexKFirst FamC.indexKSecond FamC.indexKThird FamC.indexKFourth FamC.indexWFirst FamC.indexWSecond FamC.indexWThird FamC.indexWFourth
  FamC.indexVFirst FamC.indexVSecond FamC.indexVThird FamC.indexVFourth FamC.indexFFirst FamC.indexFSecond FamC.indexFThird FamC.indexFFourth

namespace FamC
variable {I : Type} {m : ℕ} (F : FamC I m)

end FamC

section DefsC
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsC

def E8 (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 8)))

def E7 (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 7)))

namespace FamC
variable {I : Type} {m : ℕ} (F : FamC I m)

end FamC

section DefsD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsD

namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)

end Fam6

section DefsD'
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsD'

section Top6
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}

end Top6

end Formalism.LFunctionChainParameters.LChain6
