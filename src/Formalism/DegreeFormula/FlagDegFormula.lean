module

public import Mathlib

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.DegreeFormula

def dimFl (ι : Type) [Fintype ι] (N : ℕ) : ℕ := Fintype.card ι * (N * (N - 1) / 2)

def permExp {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) : (ι × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))

def degFl (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (-1) ^ dimFl ι N *
    ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * P.coeff (permExp σ)

def linRoot {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) : MvPolynomial (ι × Fin N) ℝ :=
  -∑ x : ι × Fin N, C (lam x.1 x.2) * X x

def flagDeg (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (lam : ι → Fin N → ℝ) : ℝ :=
  degFl ι N (linRoot lam ^ dimFl ι N)

def weylProd {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) : ℝ :=
  ∏ τ, ∏ i : Fin N, ∏ k : Fin N, if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1

def FlagDegFormula : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (lam : ι → Fin N → ℝ),
    flagDeg ι N lam = (Nat.factorial (dimFl ι N) : ℝ) * weylProd lam

def DegFlPowerSum : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (k : ℕ) (P : MvPolynomial (ι × Fin N) ℝ),
    1 ≤ k → degFl ι N ((∑ i : Fin N, X (τ, i) ^ k) * P) = 0

def DegFlEsymm : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (k : ℕ) (P : MvPolynomial (ι × Fin N) ℝ),
    1 ≤ k → degFl ι N (rename (fun i : Fin N => (τ, i)) (esymm (Fin N) ℝ k) * P) = 0

def DegFlHomog : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (d : ℕ) (P : MvPolynomial (ι × Fin N) ℝ),
    P.IsHomogeneous d → d ≠ dimFl ι N → degFl ι N P = 0

end Formalism.DegreeFormula
