module

public import Mathlib

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

def rI (ℓ m : ℕ) (U : Finset ℤ) (i : ℤ) : ℕ := ∑ u ∈ U.erase i, (m + padicValInt ℓ (u - i))

def cM (ℓ m : ℕ) (U : Finset ℤ) (a b : ℤ) : ℕ := ∑ i ∈ Finset.Ico a b, (2 + max 1 (rI ℓ m U i))

def cLL (ℓ m : ℕ) (U : Finset ℤ) (a b : ℤ) (d : ℕ) : ℕ := padicValNat ℓ d + cM ℓ m U a b

def c0 (ℓ m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt ℓ u)

def cTBof (ℓ s e gK c : ℕ) : ℕ :=
  c + (e + 2) * s + padicValNat ℓ e + e / (ℓ - 1) + 1 + (s + padicValNat ℓ (e + 1)) + gK

def cTB (ℓ s m e gK : ℕ) (U : Finset ℤ) : ℕ :=
  cTBof ℓ s e gK (cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)))

def TorsKilled (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [AddCommGroup A] [Module ℤ_[ℓ] A] (c : ℕ) : Prop :=
  ∀ x : A, (∃ k : ℕ, ((ℓ : ℤ_[ℓ]) ^ k) • x = 0) → ((ℓ : ℤ_[ℓ]) ^ c) • x = 0

def Rpoly (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Polynomial ℤ_[ℓ] :=
  ∏ a ∈ U.erase i, (X - C (((w ^ (i - a) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))

def HTpoly (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Polynomial ℤ_[ℓ] :=
  ∏ a ∈ U, (X - C (((w ^ (i - a) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))

def StatRVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ),
      (Rpoly ℓ w U i).eval 1 ≠ 0 ∧ PadicInt.valuation ((Rpoly ℓ w U i).eval 1) = rI ℓ m U i

def InjectivityOnLayerOfPower : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (g : Xm →ₗ[R] Xm) (k : ℕ)
    (z : R) (α : Xm ≃ₗ[R] Xm),
    (∀ x, (g ^ k) x - x = z • α x) → (∀ x : Xm, z • x = 0 → x = 0) →
    (∀ x, g x = x → x = 0) ∧ ∀ x, ∃ y, z • x = g y - y

def StatOnePlus : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (ϖ : R),
    IsAdicComplete (Ideal.span {ϖ}) Xm → ∀ E : Xm →ₗ[R] Xm,
    Function.Bijective (fun x : Xm => x + ϖ • E x)

def PerturbationOperatorIntegral : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (ϖ z : R),
    IsAdicComplete (Ideal.span {ϖ}) Xm → (∀ x : Xm, z • x = 0 → x = 0) →
    ∀ g S B : Xm →ₗ[R] Xm, (∀ x, g (S x) - S x = z • x) → (∀ x, S (g x - x) = z • x) →
    (∀ x, (g x + (z * ϖ) • B (g x)) = x → x = 0) ∧
    (∀ y, (∃ x, y = (g x + (z * ϖ) • B (g x)) - x) ↔ ∃ x, y = g x - x) ∧
    ∀ x, ∃ y, z • x = (g y + (z * ϖ) • B (g y)) - y

def StatEigen : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ) (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V),
    (∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →
    aeval g ((X - 1) * Rpoly ℓ w U i) = 0 →
    ∀ (k : ℕ) (x x' : V), ((ℓ : ℤ_[ℓ]) ^ k) • x = g x' - x' →
      ∃ y : V, ((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x = g y - y

def StatHTpoly : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ),
    HTpoly ℓ w U i ∣ (X - 1) * Rpoly ℓ w U i ∧ (i ∉ U → HTpoly ℓ w U i = Rpoly ℓ w U i)

def StatEigenInj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ), i ∉ U →
    ∀ (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V),
    (∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) → aeval g (HTpoly ℓ w U i) = 0 →
    ∀ x : V, g x = x → x = 0

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
