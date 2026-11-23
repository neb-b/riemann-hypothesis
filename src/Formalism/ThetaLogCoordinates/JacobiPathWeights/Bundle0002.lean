module

public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.Bundle0001

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.LiftWord
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {ι : Type*}

def minorF {R : Type*} [CommRing R] {n : ℕ} (m : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    (m.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det
  else 0

def actF {R : Type*} [CommRing R] {n : ℕ} (K : Form R n) (m : Matrix (Fin n) (Fin n) R) : Form R n :=
  fun J => ∑ I : Finset (Fin n), K I * minorF m I J

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementB
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def HStrip {n : ℕ} (ν μ : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ m, μ m ≤ ν m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m) ∧ ∑ m, ν m - ∑ m, μ m = (b : ℤ)

def IsPath (n : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (N : ℕ) : Prop :=
  μ 0 = 0 ∧ (∀ i ≤ N, Antitone (μ i)) ∧
    ∀ i < N, if isVec i then HStrip (μ (i + 1)) (μ i) (B i) else HStrip (μ i) (μ (i + 1)) (B i)

def colHeight {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ μ m).card

variable {ι : Type*}

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def sharpHom {k₁ ι ζ : Type*} [CommRing k₁] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (g gi : Matrix (Fin n) (Fin n) k₁) :
    MvPolynomial (LVar ι ζ n) k₁ →ₐ[k₁] MvPolynomial (LVar ι ζ n) k₁ :=
  aeval fun x =>
    match x with
    | Sum.inl (i, a) =>
      if i ∈ S then
        (if isVec i then Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a
        else Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a)
      else X (Sum.inl (i, a))
    | Sum.inr z => X (Sum.inr z)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

