module

public import Mathlib
public import Formalism.GaussValuationBounds.Statement
public import Formalism.GaussValuationBounds.Bundle0001
public import Formalism.FrobeniusContraction.Bundle0001

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

def sigUp (ℓ E M j : ℕ) : ℕ :=
  ⌈((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌉₊ + 1

def SigBoundUp : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (g h j : ℕ), 1 ≤ j →
    (sigUp ℓ (3 * g) ((h + 2 * g) / (ℓ - 1) + 1) j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4

def EisE {O : Type} [CommRing O] (ϖ : O) (e : ℕ) (E : Polynomial O) (N : ℕ) : Prop :=
  E.Monic ∧ E.natDegree = N ∧ (∀ i < N, E.coeff i ∈ Ideal.span {ϖ ^ e}) ∧ E.coeff 0 ∉ Ideal.span {ϖ ^ (e + 1)}

def GaussEisRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (x : ℝ), 0 ≤ x → ∀ (E : Polynomial O) (N : ℕ), 1 ≤ N → EisE ϖ e E N →
      Formalism.NOK.gaussV x (E : PowerSeries O) = ENNReal.ofReal (min (e : ℝ) (x * N))

def LemmaCValRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (ℓ : ℕ), 2 ≤ ℓ →
    ∀ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O),
      (∀ s, EisE ϖ e (E s) (ℓ ^ s)) → (∀ s, IsUnit (u s)) →
      ∀ (ell g a b₀ b₁ s₀ s₁ k : ℕ), s₀ < s₁ →
        2 * ((a : ℝ) + 2 * e * g * ell) < e * b₁ → 2 * b₀ ≤ ℓ * b₁ →
        PowerSeries.C (ϖ ^ a) *
            (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
            (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
          Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} →
        (k : ℝ) ≤ ((a : ℝ) + 2 * e * g * ell) * b₁ / (b₁ - b₀ / ℓ) ∧
          (k : ℝ) ≤ 2 * ((a : ℝ) + 2 * e * g * ell)

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
