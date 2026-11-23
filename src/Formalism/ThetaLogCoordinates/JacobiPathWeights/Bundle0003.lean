module

public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.Bundle0002

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def nthElt {n : ℕ} (J : Finset (Fin n)) (a : ℕ) : ℕ := ((J.sort (· ≤ ·)).map Fin.val).getD a n

def SemiStd {n C : ℕ} (T : Fin C → Finset (Fin n)) : Prop :=
  ∀ c c' : Fin C, c.val + 1 = c'.val → ∀ a < (T c').card, nthElt (T c) a ≤ nthElt (T c') a

def initSeg (n h : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < h

def genX (k : Type*) [CommRing k] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  Matrix.of fun a b => X (a, b)

def tabMinors (k : Type*) [CommRing k] {n C : ℕ} (T : Fin C → Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) k :=
  ∏ c, minorF (genX k n) (initSeg n (T c).card) (T c)

def tabDiag {n C : ℕ} (T : Fin C → Finset (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ c, ∑ b ∈ T c, ∑ a : Fin n,
    if a.val = ((T c).filter (· < b)).card then Finsupp.single (a, b) 1 else 0

def LemmaA : Prop :=
  ∀ (k : Type) [Field k] (n C : ℕ),
    LinearIndependent k (fun T : {T : Fin C → Finset (Fin n) // SemiStd T} => tabMinors k T.1)

def pathWord {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) : ℕ → Form R n
  | 0 => oneF
  | i + 1 =>
    if colHeight (μ (i + 1)) c = colHeight (μ i) c then pathWord isVec μ c Xr i
    else stepF (isVec i == decide (1 ≤ c)) (pathWord isVec μ c Xr i) (Xr i)

def canIdx {n : ℕ} (μN : Fin n → ℤ) (c : ℤ) : Finset (Fin n) :=
  if 1 ≤ c then univ.filter fun m => m.val < colHeight μN c
  else univ.filter fun m => colHeight μN c ≤ m.val

def psiPath (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ)
    (I : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) R :=
  ∏ᶠ c : ℤ, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)

def IsIndex {n : ℕ} (μN : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  ∀ c : ℤ, (I c).card = if 1 ≤ c then colHeight μN c else n - colHeight μN c

def PsiDegrees : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I →
    (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)).Finite ∧
    ∀ i : ℕ, IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (psiPath R isVec μ N I) (if i < N then B i else 0)

def PathProductLinearIndependent : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (ν : Fin n → ℤ),
    LinearIndependent k
      (fun P : {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = ν ∧ ∀ i, N < i → μ i = 0} =>
        psiPath k isVec P.1 N (canIdx ν))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementC
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def FactX2wedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X : Fin n → R) (m : Matrix (Fin n) (Fin n) R),
    actF (wedgeF K X) m = wedgeF (actF K m) (Matrix.vecMul X m)

def FactX2contr : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (Y : Fin n → R) (m : (Matrix (Fin n) (Fin n) R)ˣ),
    actF (contrF K Y) (↑m : Matrix _ _ R) =
      contrF (actF K (↑m : Matrix _ _ R)) (Matrix.vecMul Y (↑m⁻¹ : Matrix _ _ R).transpose)

def MinorMap : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ) (m : Matrix (Fin n) (Fin n) R)
    (I J : Finset (Fin n)), φ (minorF m I J) = minorF (m.map φ) I J

def ContractWedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X Y : Fin n → R),
    contrF (wedgeF K X) Y = (fun I => (∑ a, X a * Y a) * K I) - wedgeF (contrF K Y) X

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

