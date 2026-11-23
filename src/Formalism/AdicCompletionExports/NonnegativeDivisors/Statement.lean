module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.QuotientMetricDivisors.SixthReductionExplicit

@[expose] public section

noncomputable section

namespace Formalism.AdicCompletionExports.NonnegativeDivisors

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

structure NRec where

  Pl : Type

  supp : Finset Pl

  tw : Pl → Prop

  lwP : Pl → ℝ

  logWeight_nonneg : ∀ w, 0 ≤ lwP w

  ramIdx : Pl → ℕ

  etaJ : ℕ → Pl → ℚ

  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w

  dZ0 : ℕ → ℕ

  m : ℕ

  f : ℕ

  b : ℝ

  L : ℝ

  x : ℝ

  Nc : ℝ

  vvTerm : ℕ → ℝ

namespace NRec

variable (R : NRec)

def lifts : Finset ℕ := Finset.Icc 1 R.m


end NRec

section Ties

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
  (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (R : NRec)
  (ι : HeightOneSpectrum (𝓞 K) → R.Pl) (lift : J → ℕ)

def TieInj : Prop := Set.InjOn ι Tw

def TieLw : Prop := ∀ y ∈ Tw, Formalism.DivisionValues.lw y = R.lwP (ι y)

def TieRam : Prop := ∀ y ∈ Tw, (Formalism.EigenvalueLevelCeiling.ramw y : ℝ) = (R.ramIdx (ι y) : ℝ)

def TieTw : Prop := ∀ y ∈ Tw, ι y ∈ R.supp ∧ R.tw (ι y)

def TieLift : Prop := ∀ j, lift j ∈ R.lifts

def TieEta : Prop := ∀ y ∈ Tw, ∀ j, ((F.etaJ P ψ Zs j (μ y) y : ℚ) : ℝ) = (R.etaJ (lift j) (ι y) : ℝ)

def TieRank : Prop :=
  ∀ j, (R.dZ0 (lift j) : ℝ) = ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0) : ℝ)

structure Ties : Prop where
  inj : TieInj Tw R ι
  lw : TieLw Tw R ι
  ram : TieRam Tw R ι
  tw : TieTw Tw R ι
  lifts : TieLift R lift
  eta : TieEta F P ψ Zs μ Tw R ι lift
  rank : TieRank F P ψ Zs R lift

end Ties

end Formalism.AdicCompletionExports.NonnegativeDivisors
