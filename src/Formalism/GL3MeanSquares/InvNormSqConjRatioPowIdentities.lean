module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.GL3MeanSquares.Bundle0003
public import Formalism.GL3MeanSquares.Bundle0001
public import Formalism.GL3MeanSquares.Bundle0005
public import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound

@[expose] public section

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.GlobalBoundRefinements


open Formalism.HermitianLattices.GL2PrimeSums in
def ShortIntervalLowerBound : Prop :=
  ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb →
    ∃ C₀' c : ℝ, C₀ ≤ C₀' ∧ 0 < c ∧
      ∀ (B G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ) (η' : ℝ → ℝ),
        4 ≤ B → 1 ≤ G → G ≤ B → θ ∈ ({-1, 0, 1} : Set ℤ) →
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) →
        (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) →
        (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log B) →
        (∀ Y : ℝ, B ^ C₀ ≤ Y →
          |G * ((π₁ Y : ℝ) + π₂ Y + η' Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y) →
        ∀ X : ℝ, B ^ C₀' ≤ X →
          c * B ^ (-5 : ℝ) * X / Real.log X ≤ Emain θ β X ∧
          ∀ h : ℝ, h ≤ 1 → rhoErr Cr cr B X ≤ h / 100 → B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
            c * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X



open Formalism.HermitianLattices.GL2PrimeSums in
def PrimeCountAsymptoticInProgressions (C₀ Cr cr cb : ℝ) : Prop :=
  ∀ m a : ℕ, 3 ≤ m → Nat.Coprime a m → ∃ (θ : ℤ) (β : ℝ) (η' : ℝ → ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
    (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
    (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log (4 * m)) ∧
    ∀ Y : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y →
      |(m.totient : ℝ) * ((((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ) + η' Y) - Emain θ β Y|
        ≤ rhoErr Cr cr (4 * m) Y * Emain θ β Y


open Formalism.HermitianLattices.GL2PrimeSums in
def ShortIntervalImpliesProgressions : Prop :=
  ShortIntervalLowerBound → ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb → PrimeCountAsymptoticInProgressions C₀ Cr cr cb →
    ∃ C₀' c : ℝ, 0 < C₀' ∧ 0 < c ∧ PrimesAPInterval C₀' Cr cr c




open Formalism.LogVandermondeBounds.StandardLattice in
def LogLFunctionEulerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 2 ≤ M →
    Multipliable (fun P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsMaximal} =>
      Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
    0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
    |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M)

end Formalism.HermitianLattices.GlobalBoundRefinements
