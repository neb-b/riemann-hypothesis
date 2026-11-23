module

public import Formalism.TorsionNormIteration.InvIntegralOfClass

@[expose] public section

noncomputable section

open PowerSeries

universe u v w

namespace Formalism.FG

open Formalism.G Formalism.LT

section Laws

variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]

def IsIdMod2 (f : ι → MvPowerSeries ι R) : Prop :=
  (∀ j, MvPowerSeries.constantCoeff (f j) = 0) ∧
  ∀ j i, MvPowerSeries.coeff (Finsupp.single i 1) (f j) = if i = j then 1 else 0

end Laws

section FunEq

variable {K : Type u} [NormedField K]

def IsFunEqTypeV {ι : Type v} [Fintype ι] {τ : Type w} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) (g : ι → MvPowerSeries τ K) : Prop :=
  ∀ j, IntegralMv (g j - (p : K)⁻¹ •
    ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (g k)))

def IntegralMat {ι : Type v} (M : ι → ι → K) : Prop := ∀ j k, ‖M j k‖ ≤ 1

end FunEq

def FunEqHomV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ι → ι → K), IntegralMat M →
    ∀ f : ι → MvPowerSeries ι K, IsIdMod2 f → IsFunEqTypeV p q hq σ M f →
    ∀ (τ : Type w) [Finite τ] (g : ι → MvPowerSeries τ K),
      (∀ j, MvPowerSeries.constantCoeff (g j) = 0) → IsFunEqTypeV p q hq σ M g →
      ∃ h : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) ∧
        (∀ i, IntegralMv (h i)) ∧ ∀ j, MvPowerSeries.subst h (f j) = g j

def zlToW (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* WittVector l (AlgebraicClosure (ZMod l)) :=
  (WittVector.map (algebraMap (ZMod l) (AlgebraicClosure (ZMod l)))).comp
    (WittVector.equiv l).symm.toRingHom

def WittCharZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], CharZero (WittVector l (AlgebraicClosure (ZMod l)))

def WittTeichRoot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d : ℕ), 1 ≤ d →
    ∃ ζ : WittVector l (AlgebraicClosure (ZMod l)), IsPrimitiveRoot ζ (l ^ d - 1)

end Formalism.FG
