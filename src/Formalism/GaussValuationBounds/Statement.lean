module

public import Mathlib
public import Formalism.WindowSums.Statement
public import Formalism.FrobeniusContraction.Bundle0001

@[expose] public section

noncomputable section

namespace Formalism.NOK

open Polynomial

def sigNOK (ℓ E M j : ℕ) : ℕ :=
  ⌊((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1

def SigNum : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ → ∀ (E M j r : ℕ), 1 ≤ j →
    ((ℓ - 1) * r < E → r + padicValNat ℓ r.factorial < sigNOK ℓ E M j) ∧
    (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) -
        max 0 (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) ≤ sigNOK ℓ E M j

def RelVanish : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) (X u : A) (p : ℕ → A) (E M j r : ℕ),
    M ≤ r → E ≤ (ℓ - 1) * r →
    (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r ∈
      Ideal.span {X ^ M * ∏ s ∈ Finset.range j, p s ^ E}

def PhiIterX : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Formalism.WachCohomologyFacts.Base O A) (j : ℕ),
    ∃ v : A, IsUnit v ∧
      (⇑B.φ)^[j] B.X = v * B.X * ∏ s ∈ Finset.range j, B.p s ^ (B.ℓ - 1)

def PsIdeal : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Formalism.WachCohomologyFacts.Base O A) (s : ℕ),
    B.p s ∈ Ideal.span {(B.ℓ : A), B.X ^ (B.ℓ ^ s)}

def DUDeg : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (ϖ : O), Prime ϖ →
    ∀ (ℓ : ℕ) (p₀ p₁ v₀ v₁ w : PowerSeries O) (s₀ s₁ b₀ b₁ : ℕ),
      s₀ < s₁ → b₀ < ℓ * b₁ → IsUnit v₀ → IsUnit v₁ → IsUnit w →
      p₀ - v₀ * PowerSeries.X ^ (ℓ ^ s₀) ∈ Ideal.span {PowerSeries.C ϖ} →
      p₁ - v₁ * PowerSeries.X ^ (ℓ ^ s₁) ∈ Ideal.span {PowerSeries.C ϖ} →
      w * p₀ ^ b₀ ∉ Ideal.span {PowerSeries.C ϖ, p₁ ^ b₁}

def LemmaCVal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (ℓ : ℕ), 2 ≤ ℓ →
    ∀ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O),
      (∀ s, (E s).IsEisensteinAt (Ideal.span {ϖ})) → (∀ s, (E s).natDegree = ℓ ^ s) →
      (∀ s, IsUnit (u s)) →
      ∀ (ell g a b₀ b₁ s₀ s₁ k : ℕ), s₀ < s₁ →
        2 * ((a : ℝ) + 2 * g * ell) < b₁ → 2 * b₀ ≤ ℓ * b₁ →
        PowerSeries.C (ϖ ^ a) *
            (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
            (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
          Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} →
        (k : ℝ) ≤ ((a : ℝ) + 2 * g * ell) * b₁ / (b₁ - b₀ / ℓ) ∧
          (k : ℝ) ≤ 2 * ((a : ℝ) + 2 * g * ell)

def KapBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell g h : ℕ) (a : Fin 5 → ℤ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun t => Finset.Ico (a t) (a t + 4 * (g : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ 2 * (h : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        ell + 20 * g * (1 + ell) + 5 * (4 * g / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * h))

def CjExist : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∃ c : ℤ → ℤ_[ℓ], (∀ j, -(ℓ : ℤ_[ℓ]) * c j = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) ∧ c 0 = 0 ∧
      ∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')

end Formalism.NOK
