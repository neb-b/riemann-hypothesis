module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.LogVandermondeBounds.Bundle0001
public import Formalism.LogVandermondeBounds.Bundle0002

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.MassLowerBoundClosed
section
open NumberField Finset

namespace Formalism.HermitianLattices.SiegelMassBounds

def SiegelMassRatioThm : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

end Formalism.HermitianLattices.SiegelMassBounds
end

-- bundled from Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset MeasureTheory
open Formalism.LogVandermondeBounds.StandardLattice

def SW_hecke_gap : Prop :=
  ∀ (q : ℝ) (M : ℕ), 2 ≤ q → 3 ≤ M →
    q ^ 2 + q < q ^ M + q - 1 + q ^ (2 - (M : ℤ)) ∧
    ∀ S : ℝ, 0 ≤ S → (q ^ M + q - 1 + q ^ (2 - (M : ℤ))) * S ≤ (q ^ 2 + q) * S → S = 0

def GlobalArithmeticIdentity : Prop :=
  ∀ (f M : ℕ) (v Lv : ℝ), 1 ≤ M → 0 < v → 0 < Lv →
    let dF : ℝ := (2 * v) ^ f
    let cM : ℝ := (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)
    (cM ^ f * dF ^ ((1 : ℝ) / 2 - M) / Lv)⁻¹ =
      (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f / Real.sqrt dF * Lv

def LogLFunctionEulerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 3 ≤ M →
    Multipliable (fun P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsMaximal} =>
      Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
    0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
    |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M)

def LocalColumnIndex : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ), 2 ≤ m → Even m → 3 ≤ Fintype.card F →
    let g : ℝ := Fintype.card F
    let r := k + m - 1
    let rS := m / 2 - 1
    let dimN := (r ^ 2 - (k + 1) ^ 2 - 2 * rS) / 2
    (∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧
      (Fintype.card (GL (Fin k) F) : ℝ) / g ^ (k * (k - 1) / 2) = g ^ (k * (k + 1) / 2) * θ) ∧
    (∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧
      (Fintype.card (GL (Fin r) F) : ℝ) / (g ^ dimN * g ^ (k * (k - 1) / 2)) =
        g ^ ((r ^ 2 + 3 * k + 1 + 2 * rS) / 2) * θ)

def IndexRatioComparison : Prop :=
  ∀ (f k m : ℕ) (g₁ g₂ Ipi Isig : ℝ) (θ θ' : Fin 2 → ℕ → ℝ), 2 ≤ m → Even m → 1 ≤ g₁ → 1 ≤ g₂ →
    (∀ i ρ, 1 / 2 ≤ θ i ρ ∧ θ i ρ ≤ 1 ∧ 1 / 2 ≤ θ' i ρ ∧ θ' i ρ ≤ 1) →
    let r := k + m - 1
    let rS := m / 2 - 1
    let g : Fin 2 → ℝ := ![g₁, g₂]
    Ipi = ∏ i, ∏ ρ ∈ range f, g i ^ (k * (k + 1) / 2) * θ i ρ →
    Isig = ∏ i, ∏ ρ ∈ range f, g i ^ ((r ^ 2 + 3 * k + 1 + 2 * rS) / 2) * θ' i ρ →
    ((2 : ℝ) ^ (2 * f))⁻¹ * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi ∧
    Isig / Ipi ≤ (2 : ℝ) ^ (2 * f) * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2)

def LeastNoncompactGap : Prop :=
  ∀ (k m : ℕ) (v b : ℕ → ℝ) (h₀ : ℝ), 1 ≤ k → 0 ≤ h₀ →
    (∀ i, i < k - 1 → 0 ≤ v i) → 0 < b 0 → (∀ j, j + 1 < m → h₀ ≤ b (j + 1) - b j) →
    ∀ i j, i < j → j < k - 1 + m → plusSign k i ≠ plusSign k j →
      h₀ ≤ rowPar k v b i - rowPar k v b j

def PowerProductTwoSidedBounds : Prop :=
  ∀ (f k : ℕ) (T X Γ Dstar dstar dM lo hi : ℝ), 1 ≤ f → 1 ≤ k → 2 * f ≤ 2 ^ k → 2 ≤ T → 0 < X → 1 ≤ Γ →
    0 < Dstar → 0 < dstar → X ^ (f * k) = Dstar / dstar →
    X * Γ ^ (-(2 : ℝ) / ((f : ℝ) * k)) ≤ T →
    T ≤ X * Γ ^ (-(2 : ℝ) / ((f : ℝ) * k)) * (1 + 1 / ((f : ℝ) * k)) →
    dM = dstar * (T ^ k - 1) ^ f →
    lo ≤ Real.log X → Real.log X ≤ hi →
    Dstar * (Γ⁻¹) ^ 2 / 2 ≤ dM ∧ dM ≤ Real.exp 1 * (Dstar * (Γ⁻¹) ^ 2) ∧
    Real.log T ≤ hi + Real.log 2 ∧ lo - 2 * Real.log Γ / ((f : ℝ) * k) ≤ Real.log T

end Formalism.HermitianLattices.GenusMassVolumes
end

