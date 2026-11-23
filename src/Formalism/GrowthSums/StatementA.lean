module

public import Mathlib
public import Formalism.SubspaceCounting.Bundle0001

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def coarseUnit (P n : ℕ) : ℚ :=
  ((P * n).factorial : ℚ) / (((P.factorial : ℚ) ^ n) * (n.factorial : ℚ))

def CoarseUnitProd : Prop :=
  ∀ P n : ℕ, 1 ≤ P →
    coarseUnit P n = ∏ i ∈ range n, ∏ y ∈ Ico 1 P, (1 + (P : ℚ) * i / y)

def HarmonicVal : Prop :=
  ∀ p t s : ℕ, p.Prime →
    (s : ℤ) ≤ padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * ∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s)

def PowerSumPoly : Prop :=
  ∀ s : ℕ, ∃ f : Polynomial ℚ, f.natDegree = s + 1 ∧
    ∀ n : ℕ, f.eval (n : ℚ) = ∑ i ∈ range n, (i : ℚ) ^ s

def rhoP (p : ℝ) : ℝ := 1 / (p ^ 2 - 1)

def gamP (p : ℝ) : ℝ := p * rhoP p

def GammaIdentity : Prop :=
  ∀ p : ℝ, 1 < p →
    HasSum (fun n : ℕ => (p ^ (2 * n + 1))⁻¹) (gamP p) ∧ gamP p = 1 / (p - 1) - rhoP p

def gainG {n : ℕ} (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de : ℝ) : ℝ :=
  gamP p * ∑ s ∈ TT, al s -
    ∑ s ∈ TTodd, ∑' e : ℕ, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) - de

def excessGain {n : ℕ} (p : ℝ) (TT : Finset (ZMod n)) (D : ZMod n → Finset ℕ) (al cap : ZMod n → ℝ)
    (de : ℝ) : ℝ :=
  ∑ s ∈ TT, ∑' e : ℕ,
    (if 2 * e + 1 ∈ D s then 0 else max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)
    - de

end Formalism.GrowthSums
