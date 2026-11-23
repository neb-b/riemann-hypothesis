module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

def gramOf {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  gᴴ * diagonal (fun i => (hd i : ℂ)) * g

def gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    Matrix {a : Fin N // (a : ℕ) < k} {a : Fin N // (a : ℕ) < k} ℂ :=
  (gramOf hd g).submatrix Subtype.val Subtype.val

def gramLog {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 / 2) * Real.log ‖(gramHead hd k g).det‖

def sigForm (N j : ℕ) : Fin N → ℝ := fun a => if (a : ℕ) < N - j then -1 else 1

def InFlagDomain (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsUnit g.det ∧ (-gramHead (sigForm N j) (N - j) g).PosDef

def stepPot (N j : ℕ) (i : Fin N) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if (i : ℕ) + 1 ≤ j then gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) g - gramLog (sigForm N j) (N - j) g
  else gramLog (sigForm N j) N g - gramLog (sigForm N j) (N - j) g + gramLog (sigForm N j) ((i : ℕ) + 1 - j) g

def herm2 (G : Matrix (Fin 2) (Fin 2) ℂ) (u w : Fin 2 → ℂ) : ℂ := star u ⬝ᵥ (G *ᵥ w)

def xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℝ :=
  -Real.log (herm2 G ![1, a] ![1, a]).re + (1 / 2) * Real.log G.det.re

def logSin (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) : ℝ :=
  (1 / 2) * Real.log (1 - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 /
    ((herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re))

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial

def formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) : MvPolynomial σ ℝ :=
  ∑ w : Fin n → σ, C (a w) * ∏ j, X (w j)

variable {Ψ : Type} {N : ℕ}

def gapX (p : Ψ × Fin N) : MvPolynomial (Ψ × Fin N) ℝ :=
  X p - if h : (p.2 : ℕ) + 1 < N then X (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

def gap (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) : ℝ := eval lam (gapX p)

def Dominant (lam : Ψ × Fin N → ℝ) : Prop := ∀ p : Ψ × Fin N, (p.2 : ℕ) + 1 < N → 0 ≤ gap lam p

def toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ := aeval gapX

def toWtS : MvPolynomial (Option (Ψ × Fin N)) ℝ →ₐ[ℝ] MvPolynomial (Option (Ψ × Fin N)) ℝ :=
  aeval fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)

def gapS (lam : Ψ × Fin N → ℝ) (s : ℝ) : Option (Ψ × Fin N) → ℝ := fun o => o.elim s (gap lam)

def xiCoef [DecidableEq Ψ] (τ : Ψ) (a : Fin N) (p : Ψ × Fin N) : ℤ :=
  if p.1 = τ then
    (if (p.2 : ℕ) + 1 = a then 1 else 0) + (if (p.2 : ℕ) = a + 1 then 1 else 0) - (if p.2 = a then 2 else 0)
  else 0

def linePoly {σ : Type} (c : σ → ℝ) (e : σ → ℤ) (Q : MvPolynomial σ ℝ) : Polynomial ℝ :=
  aeval (fun a => Polynomial.C (c a) - Polynomial.C ((e a : ℝ) / 2) * Polynomial.X) Q

def rhoWt (Ψ : Type) (N : ℕ) : Ψ × Fin N → ℝ := fun p => -((p.2 : ℕ) : ℝ)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

