module

public import Mathlib

@[expose] public section

noncomputable section

namespace Formalism.WindowSums

open PowerSeries

def p1 {O : Type} [CommRing O] (ℓ : ℕ) (ε u : PowerSeries O) : PowerSeries O :=
  PowerSeries.C (ℓ : O) * ε + u * PowerSeries.X ^ ℓ

def DistinctTerms : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (ϖ : O), ϖ ≠ 0 → ¬ IsUnit ϖ →
    ∀ {ι : Type} (I : Finset ι) (w : ι → PowerSeries O) (e m : ι → ℕ) (B s : ℕ),
      (∀ i ∈ I, IsUnit (w i)) → Set.InjOn e I →
      ((∑ i ∈ I, w i * PowerSeries.X ^ e i * PowerSeries.C (ϖ ^ m i)) ∈
          Ideal.span {(PowerSeries.X : PowerSeries O) ^ B, PowerSeries.C (ϖ ^ s)} ↔
        ∀ i ∈ I, B ≤ e i ∨ s ≤ m i)

def ZpowVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ j : ℤ, j ≠ 0 →
      (((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 ∧
        PadicInt.valuation (((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s + padicValInt ℓ j)

def ValProd : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    (∀ M : ℕ, (∏ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i)) ≠ 0 ∧
      PadicInt.valuation (∏ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i)) =
        M * s + padicValNat ℓ M.factorial) ∧
    (∀ J : Finset ℤ, 0 ∉ J →
      (∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) ≠ 0 ∧
      PadicInt.valuation (∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) =
        J.card * s + ∑ j ∈ J, padicValInt ℓ j)

def PP (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]ˣ) (ell : ℕ) (JJ : Finset ℤ) : Polynomial ℤ_[ℓ] :=
  (∏ i ∈ JJ.erase 0,
      (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
    ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k

def KillerVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (c : ℤ_[ℓ]ˣ), PadicInt.valuation ((c : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell : ℕ) (JJ : Finset ℤ),
      (PP ℓ c ell JJ).eval 1 ≠ 0 ∧
      PadicInt.valuation ((PP ℓ c ell JJ).eval 1) =
        ∑ i ∈ JJ.erase 0, (1 + ell + padicValInt ℓ i) + ell

def KillerKills : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]ˣ) (ell : ℕ) (JJ : Finset ℤ)
    (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (T : Module.End ℤ_[ℓ] V),
    (∀ x : V, (∃ i ∈ JJ.erase 0, (T ^ (ℓ ^ ell)) x = ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x) →
      Polynomial.aeval T (PP ℓ c ell JJ) x = 0) ∧
    (∀ v : V, (T ^ (ℓ ^ ell)) v = v → Polynomial.aeval T (PP ℓ c ell JJ) (T v - v) = 0)

def WindowSum : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℤ) (L D : ℕ) (S : Finset ℤ),
    S ⊆ Finset.Ico a (a + L) → 0 ∉ S → (∀ i ∈ S, |i| ≤ D) →
    ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) ≤ (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D

def RSplit : Prop :=
  ∀ (R : Type) [CommRing R] (P : Polynomial R), ∃ P₁ : Polynomial R,
    P - Polynomial.C (P.eval 1) = (Polynomial.X - 1) * P₁ ∧
    ∀ (V : Type) [AddCommGroup V] [Module R V] (T : Module.End R V) (w : V),
      P.eval 1 • w = Polynomial.aeval T P w - (T (Polynomial.aeval T P₁ w) - Polynomial.aeval T P₁ w)

def Lagrange : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [AddCommGroup V] [Module R V]
    (T : Module.End R V) {ι : Type} [DecidableEq ι] (I S : Finset ι) (γ : ι → R) (d : R) (x : V),
    S ⊆ I → Set.InjOn γ I →
    Polynomial.aeval T (∏ k ∈ S, (Polynomial.X - Polynomial.C (γ k))) x = 0 →
    Polynomial.aeval T (∏ k ∈ I \ S, (Polynomial.X - Polynomial.C (γ k))) x = 0 →
    (∀ k ∈ I, (∏ m ∈ I.erase k, (γ k - γ m)) ∣ d) →
    d • x = 0

end Formalism.WindowSums
