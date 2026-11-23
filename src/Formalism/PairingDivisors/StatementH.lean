module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0001

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

abbrev Pl (K : Type) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

def meanInf (K : Type) [Field K] [NumberField K] (φ : InfinitePlace K → ℝ) : ℝ :=
  (2 / (finrank ℚ K : ℝ)) * ∑ v, φ v

def wt {K : Type} [Field K] [NumberField K] [StarRing K] (S : Finset ℕ) (c : ℕ → ℝ) (w : Pl K) : ℝ :=
  ∑ l ∈ S, c l * (vw w (l : K) : ℝ)

def SumValNat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ),
    (Function.support fun w : Pl K => lw w * (vw w (n : K) : ℝ)).Finite ∧
    ∑ᶠ w : Pl K, lw w * (vw w (n : K) : ℝ) = Real.log n

def WtSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (S : Finset ℕ) (c : ℕ → ℝ),
    (Function.support fun w : Pl K => lw w * wt S c w).Finite ∧
    ∑ᶠ w : Pl K, lw w * wt S c w = ∑ l ∈ S, c l * Real.log l ∧
    ((∀ l ∈ S, 0 ≤ c l) → ∀ w : Pl K, 0 ≤ wt S c w)

def HeightCore : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    (a De : K) (M nff : ℕ) (o vA : Pl K → ℤ) (S : Finset ℕ) (N0 : ℕ → ℝ),
    a ≠ 0 → De ≠ 0 →
    (∀ w, vw w De = -12 * o w) →
    (∀ w, vw w a + M * o w ≤ vA w) →
    (∀ w, vA w ≤ vw w a + M * o w + M * vw w (nff : K)) →
    (∀ l ∈ S, 0 ≤ N0 l) →
    (∀ w, - wt S N0 w ≤ (vA w : ℝ)) →
    (Function.support fun w : Pl K => lw w * |(vA w : ℝ)|).Finite ∧
    ∑ᶠ w : Pl K, lw w * |(vA w : ℝ)| ≤
      (1 / 12) * meanInf K (fun v => Real.log ‖v.embedding (a ^ 12 * (De ^ M)⁻¹)‖)
        + M * Real.log nff + 2 * ∑ l ∈ S, N0 l * Real.log l

def absK {Φ : Type} [Fintype Φ] (κ : Φ → ℕ) : ℕ := ∑ τ, κ τ

def wtM {Φ : Type} [Fintype Φ] (k : ℕ) (κ : Φ → ℕ) : ℕ := k * Fintype.card Φ + 2 * absK κ

def cmConst {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) : ℝ :=
  dF ^ (((k : ℝ) - 1) / 2) * (∏ τ, Real.Gamma ((k : ℝ) + κ τ)) * (2 * Real.pi / Real.sqrt d) ^ absK κ

def BB {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) (p_power_smul_sub_sum LB : ℝ) (nff : ℕ) (SN : ℝ) : ℝ :=
  (((k : ℝ) - 1) / 2) * Real.log dF + ∑ τ, Real.log (Real.Gamma ((k : ℝ) + κ τ))
    + (absK κ : ℝ) * Real.log (2 * Real.pi)
    + (((k : ℝ) * Fintype.card Φ + absK κ) / 2) * Real.log d
    + ((wtM k κ : ℝ) / 2) * |p_power_smul_sub_sum| + LB + (wtM k κ : ℝ) * Real.log nff + 2 * SN

end Formalism.PairingDivisionLocalBalance
