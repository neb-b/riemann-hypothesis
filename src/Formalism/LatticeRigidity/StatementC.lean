module

public import Mathlib

@[expose] public section

namespace Formalism.SA.C

open Finset Real NumberField

def RecHyp (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ s 0 ≤ M ∧ (∀ i, 0 ≤ s i) ∧
  (∀ i, 1 ≤ i → i ≤ r + 1 →
    √(s i) ≤ (1 + ε) * √(s (i-1)) + ∑ t ∈ Icc 2 i, δ ^ (t-1) * √(s (i-t))) ∧
  m 0 = 1 ∧
  (∀ i, 1 ≤ i → i ≤ r + 1 →
    √(m i) ≤ √(m (i-1) + ε * s (i-1)) * (1 + ε) + ∑ t ∈ Icc 2 i, δ ^ (t-1) * √(s (i-t))) ∧
  r * (ε + δ) ≤ 1/10

def RecursionUnrestricted : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ), RecHyp r ε δ M s m →
    (∀ i ≤ r + 1, s i ≤ 2 * M) ∧ √(m (r+1)) ≤ 1 + C * r * (ε * M + δ * √M)

noncomputable def chebPt (α β : ℝ) (n : ℕ) (j : Fin (n+1)) : ℝ :=
  (α + β) / 2 + (β - α) / 2 * Real.cos (π * (j : ℕ) / n)


open NumberField in
def BoxSum : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), b ≠ 0 →
    ∀ (x : InfinitePlace E → ℝ) (Θ Kx : ℝ), (∀ w, 0 < x w) → 2 < Θ → 3 ≤ Kx →
      Θ ^ Fintype.card (InfinitePlace E) =
        √(FractionalIdeal.absNorm b : ℝ) / ∏ w, x w →
      ∀ S : Finset E, (∀ l ∈ S, l ∈ b ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
          (C * Θ ^ (-(Kx - 5/2))) ^ Fintype.card (InfinitePlace E)

end Formalism.SA.C
