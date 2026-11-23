module

public import Formalism.LFunctionBounds.Statement

@[expose] public section

open Complex

noncomputable section

namespace Formalism.FX

open Classical

def Lerch : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 1 →
    HasDerivAt (fun s : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s)
      (((Real.log (Real.Gamma a) - Real.log (2 * Real.pi) / 2 : ℝ)) : ℂ) 0

def DivisorBound : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ e

def LPartialSum : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ B : ℝ,
    (∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q)‖ ≤ B) →
    ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N →
      ‖DirichletCharacter.LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
        2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re)

end Formalism.FX
