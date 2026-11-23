module

public import Mathlib

@[expose] public section

noncomputable section

open MvPolynomial Matrix
open scoped ContDiff

namespace PositivityTheory.RgTw

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev G (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℂ

abbrev Poly (n : ℕ) := MvPolynomial (Fin 4 × Fin n × Fin n) ℂ

def Xm (j : Fin 4) : Matrix (Fin n) (Fin n) (Poly n) := fun a b => X (j, a, b)

def ev (d : Mat n) : Poly n →+* ℂ := MvPolynomial.eval fun x => ![d, dᴴ, d⁻¹, dᴴ⁻¹] x.1 x.2.1 x.2.2

def sigP (n : ℕ) : Matrix (Fin n) (Fin n) (Poly n) := Xm 0 * Xm 1 - Xm 3 * Xm 2

def hb (p : Fin n × Fin n) : Mat n :=
  if p.1 = p.2 then Matrix.single p.1 p.1 1
  else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) • (Matrix.single p.1 p.2 1 + Matrix.single p.2 p.1 1)
  else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1)

def sP (p : Fin n × Fin n) : Poly n := Matrix.trace (sigP n * (hb p).map C)

def uM (d : Mat n) : ℝ := (∑ p, (ev d (sP p)).re ^ 2) / 2

def th (g : G n) : G n := (star g)⁻¹

theorem th_one : th (1 : G n) = 1 := by simp [th]

def tw (x d : G n) : G n := x⁻¹ * d * th x

def bas (H : ℝ → ℝ) (P : Poly n) (d : G n) : ℂ := (H (uM d.val) : ℂ) * ev d.val P

def fam (F : ℝ → ℝ) (τ : Poly n) (P : ℕ → Poly n) (t : ℝ) (d : G n) : ℂ :=
  ∑ k ∈ Finset.range (n * n + 1), ((t ^ (2 * (k : ℤ) - (n * n : ℕ)) : ℝ) : ℂ) *
    bas (fun x => iteratedDeriv k F (t ^ 2 * x)) (τ * P k) d

end PositivityTheory.RgTw
