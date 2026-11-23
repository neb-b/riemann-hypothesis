module

public import Mathlib
public import Formalism.GaussValuationBounds.Statement
public import Formalism.WindowSums.Statement
public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

@[expose] public section

-- bundled from Formalism.TruncatedSeriesCounting.AprimeArith
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

def Mpar (ℓ g h : ℕ) : ℕ := (h + 2 * g) / (ℓ - 1) + 1

def sigE (ℓ g h j : ℕ) : ℕ :=
  ⌈((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1⌉₊

def a0E (ℓ g h j ell : ℕ) (rr : ℝ) : ℝ := 2 * (sigE ℓ g h j : ℝ) + rr + 2 * g * ell

def eE (ℓ g h j ell : ℕ) (rr kap : ℝ) : ℝ :=
  2 * rr + 4 * (sigE ℓ g h j : ℝ) + 2 * a0E ℓ g h j ell rr + 2 * kap

def RrBound : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (n : ℕ) [NeZero n] (H : ZMod n → ℕ) (G h j : ℕ) (cut : ZMod n) (s r : ℝ),
    1 ≤ h → (∀ x, H x ≤ 2 * h) → (∀ k : ℕ, 1 ≤ k → k ≤ j → H (cut + k) ≤ 2 * G) →
    s ≤ ∑' a : ℕ, ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a →
    r ≤ s * ℓ / ((ℓ : ℝ) - 1) ^ 2 + (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) →
    r ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1)

def ExponentBoundOfRankAndKappaBounds : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (G g h j ell : ℕ) (rr kap : ℝ), 1 ≤ j → G ≤ g → 1 ≤ g → g ≤ h → 1 ≤ ell →
    rr ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1) →
    kap ≤ ell + 20 * g * (1 + ell) + 5 * (4 * g / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * h)) →
    eE ℓ g h j ell rr kap ≤
      800 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + (g : ℝ) * ell + Real.logb ℓ h)

def AprimeArith : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b w S η j ell b₀ b₁ : ℕ) (rr : ℝ),
    1 ≤ j → C * ((j : ℝ) + 1) * ((w + S + η : ℕ) + 1 : ℝ) ≤ b → ell ≤ 3 * j + 1 →
    b ≤ b₀ → b₀ ≤ b + η → b ≤ b₁ → b₁ ≤ b + η →
    rr ≤ 20 * (((w + S + η : ℕ) : ℝ) / ℓ + ((b + η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) +
      Real.logb ℓ (b + η + S : ℕ) + 1) →
    max (w + S + η) 1 < b₀ ∧ max (w + S + η) 1 < b₁ ∧ (b₀ : ℝ) < ℓ * b₁ ∧ (b₀ : ℝ) ≤ ℓ * b₁ / 2 ∧
      a0E ℓ (max (w + S + η) 1) (b + η + S) j ell rr < (b₁ : ℝ) / 2

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

-- bundled from Formalism.TruncatedSeriesCounting.PowMemSpanOfMemSpanLinearDistinguished
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open PowerSeries

def KapWin : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell K D : ℕ) (a : Fin K → ℤ) (L : Fin K → ℕ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun k => Finset.Ico (a k) (a k + (L k : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ (D : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        (ell : ℝ) + ((∑ k, L k : ℕ) : ℝ) * (1 + ell) +
          ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)

def ColTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z I : Submodule O M) (s s₀ : Finset M),
    I ≤ Z → s.card ≤ g → s₀.card ≤ g₀ → (↑s₀ : Set M) ⊆ Z →
    Submodule.span O (s : Set M) ⊔ I = Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g * e + g₀ * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end
end

-- bundled from Formalism.TruncatedSeriesCounting.StatementX
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

def QaNum : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (H' H : ℕ) (eW : ℝ), H' ≤ H →
    eW ≤ (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 3 + Real.logb ℓ ((H' : ℝ) + 1) →
    (((H' / (ℓ - 1) + 1 : ℕ)) : ℝ) + eW - 1 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H

def TruncSig : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (y X M η : ℕ),
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 ((ℓ : ℝ) * y - X) ≤ ((X : ℝ) + 1) / ((ℓ : ℝ) - 1) + 1 ∧
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 ((ℓ : ℝ) * y - η - M) ≤
      ((M : ℝ) + η) / ((ℓ : ℝ) - 1) + 1 ∧
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 (((ℓ : ℝ) - 1) * y - (X : ℝ) / ℓ) ≤
      (X : ℝ) / ((ℓ : ℝ) - 1) ^ 2 + 1

def TruncRem1 : Prop :=
  ∀ (R : Type) [CommRing R] (ℓ : ℕ), 1 ≤ ℓ → ∀ (π₀ : R) (y K c : ℕ),
    (c : ℤ) ≤ (ℓ : ℤ) * y - K →
    (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ y ∈
      Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K}

def ArcExp : Prop :=
  ∀ (r σ κ G : ℝ) (j' ell : ℕ), 0 ≤ r → 0 ≤ σ → 0 ≤ κ → 0 ≤ G → j' ≤ ell →
    r + 4 * σ + κ + max (r + κ) (2 * σ + 2 * j' * G + 1) ≤
      2 * r + 6 * σ + 2 * κ + 2 * G * ell + 1

def SatA : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (ℓ f f' : A), f' ≠ 0 →
    (∀ a : A, ℓ * a ∈ Ideal.span {f} → a ∈ Ideal.span {f}) →
    (∀ a : A, ℓ * a ∈ Ideal.span {f'} → a ∈ Ideal.span {f'}) →
    ∀ (x : FractionRing A) (k : ℕ),
      (∃ b : A, algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) f' * x) →
      (∃ a : A, algebraMap A (FractionRing A) (f * a) = algebraMap A (FractionRing A) ℓ ^ k * x) →
      ∃ a : A, x = algebraMap A (FractionRing A) (f * a)

def UnitCoefficientPowerMod : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) (ε u : PowerSeries O) (y : ℕ),
    (PowerSeries.coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) - (PowerSeries.constantCoeff u) ^ y ∈
      Ideal.span {(ℓ : O)}) ∧
    (IsLocalRing O → ¬ IsUnit (ℓ : O) → IsUnit u →
      IsUnit (PowerSeries.coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y)))

end Formalism.TruncatedSeriesCounting.X
end
end

