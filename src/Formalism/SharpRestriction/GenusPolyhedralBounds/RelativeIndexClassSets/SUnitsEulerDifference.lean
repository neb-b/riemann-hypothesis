module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Mathlib
public import Formalism.LogFactorialIndices.Bundle0001
public import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
public import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0002

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev WL (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) :
    Submodule (X.Kl la) (X.Vl la) :=
  X.locK la (X.Msup ka)

def inW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (N : Submodule (X.Ol la) (X.Vl la)) : Submodule (X.Ol la) ↥(WL X ka la) :=
  N.comap ((WL X ka la).subtype.restrictScalars (X.Ol la))

def MW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) :
    Submodule (X.Ol la) ↥(WL X ka la) :=
  inW X ka la (X.loc la (X.Msup ka))

def ThW (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) : Submodule (X.Ol la) ↥(WL X ka la) :=
  inW X ka la (X.loc la (X.Theta S ka wL wF T))

structure LocDat (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) where

  O' : Type
  K' : Type
  V₁ : Type
  [iO : CommRing O']
  [dO : IsDomain O']
  [vO : IsDiscreteValuationRing O']
  [aO : Algebra (X.Ol la) O']
  [fK : Field K']
  [aOK : Algebra O' K']
  [frK : IsFractionRing O' K']
  [aKK : Algebra (X.Kl la) K']
  [aOlK : Algebra (X.Ol la) K']
  [st1 : IsScalarTower (X.Ol la) (X.Kl la) K']
  [st2 : IsScalarTower (X.Ol la) O' K']
  [gV : AddCommGroup V₁]
  [mKV : Module K' V₁]
  [mOV : Module O' V₁]
  [st3 : IsScalarTower O' K' V₁]
  [mKlV : Module (X.Kl la) V₁]
  [st4 : IsScalarTower (X.Kl la) K' V₁]

  bc : ↥(WL X ka la) →ₗ[X.Kl la] V₁

  ϖ : X.Ol la

  K₁ : Type
  [fK₁ : Field K₁]
  [aK₁ : Algebra K' K₁]
  [fdK₁ : FiniteDimensional K' K₁]
  [sK₁ : Algebra.IsSeparable K' K₁]
  [aOK₁ : Algebra O' K₁]
  [st5 : IsScalarTower O' K' K₁]

  ι : Type
  [fι : Fintype ι]
  y : ι → X.Pt la

  ν : ι → ℝ
  ep : ι → ℕ
  f : ι → ℕ

  R : ℕ
  I : ℕ

  N₁ : Submodule O' V₁
  Z : Submodule O' V₁
  Zm : Submodule O' V₁
  N' : Submodule O' V₁

  n : ℕ
  be : ℕ
  th : Fin n → V₁
  c : V₁ →ₗ[K'] (Fin n → K₁)

  Wsec : Type
  [gWs : AddCommGroup Wsec]
  [mWs : Module O' Wsec]
  AA : Submodule O' Wsec
  AA' : Submodule O' Wsec
  N₁' : Submodule O' Wsec
  ρ : ↥N' →ₗ[O'] Wsec

  a : O'
  a' : O'

  Rr : ι → Type
  Aq : ι → Type
  [rR : ∀ z, CommRing (Rr z)]
  [lR : ∀ z, IsLocalRing (Rr z)]
  [aR : ∀ z, Algebra O' (Rr z)]
  [hR : ∀ z, IsLocalHom (algebraMap O' (Rr z))]
  [gA : ∀ z, AddCommGroup (Aq z)]
  [mRA : ∀ z, Module (Rr z) (Aq z)]
  [mOA : ∀ z, Module O' (Aq z)]
  [sRA : ∀ z, IsScalarTower O' (Rr z) (Aq z)]
  xq : ∀ z, Rr z
  nq : ι → ℕ
  Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)
  rq : ι → ℕ → ℕ

  A0 : Type
  [S_units_euler_difference : AddCommGroup A0]
  [multiplicityBound : Module O' A0]
  n1 : ℕ
  F1 : ℕ → Submodule O' ↥AA
  ι1 : Type
  [fι1 : Fintype ι1]
  [dι1 : DecidableEq ι1]
  deg : ι1 → ℕ
  δ : ℕ
  t : Fin δ → A0
  σ : ∀ k, ↥(F1 k) →ₗ[O'] ({α : ι1 // deg α = k} → A0)
  u : ι1 → Fin δ → ↥AA

attribute [instance] LocDat.iO LocDat.dO LocDat.vO LocDat.aO LocDat.fK LocDat.aOK LocDat.frK LocDat.aKK
  LocDat.aOlK LocDat.st1 LocDat.st2 LocDat.gV LocDat.mKV LocDat.mOV LocDat.st3 LocDat.mKlV LocDat.st4
  LocDat.fK₁ LocDat.aK₁ LocDat.fdK₁ LocDat.sK₁ LocDat.aOK₁ LocDat.st5 LocDat.fι LocDat.gWs LocDat.mWs
  LocDat.rR LocDat.lR LocDat.aR LocDat.hR LocDat.gA LocDat.mRA LocDat.mOA LocDat.sRA LocDat.S_units_euler_difference LocDat.multiplicityBound
  LocDat.fι1 LocDat.dι1

namespace LocDat

variable {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {la : HeightOneSpectrum (𝓞 B.KO)} (L : LocDat X ka la)

def _root_.Formalism.MainNotions.Gaps.T0.InLat (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  Formalism.LatticeIndexTer.IsLat (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) ∧
    Formalism.LatticeIndexTer.IsLat (X.Ol la) (X.Kl la) ↥(WL X ka la) (ThW X S ka wL wF T la)

end LocDat

end Formalism.MainNotions.Gaps.T0
