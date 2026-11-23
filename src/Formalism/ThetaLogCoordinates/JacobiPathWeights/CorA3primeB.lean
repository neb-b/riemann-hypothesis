module

public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def valP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithTop ℤ :=
  valS (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def lamP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithBot ℤ :=
  lam1S (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def geB (x : WithTop ℤ) (θ : WithBot ℤ) : Prop := ∀ t : ℤ, θ = (t : WithBot ℤ) → (t : WithTop ℤ) ≤ x

def leT (y : WithBot ℤ) (M : WithTop ℤ) : Prop := ∀ t : ℤ, M = (t : WithTop ℤ) → y ≤ (t : WithBot ℤ)

def GoodG {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k) : Prop :=
  geB (valP isVec i G) θ ∧ leT (lamP isVec i G) M

def psiFam (R : Type*) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    MvPolynomial (ℕ × Fin n) R :=
  psiPath R isVec x.1.1 N x.1.2

def FactSplit : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), i ≤ N → G ∈ polB k n N B →
    ∃ (T : Finset (ℕ × Fin n →₀ ℕ)) (Gc : (ℕ × Fin n →₀ ℕ) → MvPolynomial (ℕ × Fin n) k),
      (∀ β ∈ T, ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0) ∧
      (∀ β ∈ T, Gc β ∈ polB k n i B) ∧
      G = ∑ β ∈ T, Gc β * monomial β 1 ∧
      (GoodG isVec i θ M G → ∀ β ∈ T, GoodG isVec i θ M (Gc β))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
