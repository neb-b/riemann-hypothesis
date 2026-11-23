module

public import Formalism.LandauZeroFreeBounds.Statement
public import Formalism.JacobiWeightFamilies.Statement
public import Formalism.LFunctionBounds.PositivityBound

@[expose] public section

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)

def psiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]), Λ n

def ExcZeros (c₁ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) : Prop :=
  B.card ≤ 1 ∧
  (∀ β ∈ B, χ ≠ 1 ∧ InRegion c₁ q (β : ℂ) ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
    deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0) ∧
  ∀ s : ℂ, InRegion c₁ q s → IsLZero χ s → ∃ β ∈ B, s = (β : ℂ)

def PsiChiBound : Prop :=
  ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (x : ℝ), ExcZeros c₁ χ B → 2 ≤ x →
      (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))

def SiegelLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
    c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖

def SiegelWalfisz : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c C : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x → (q : ℝ) ≤ Real.log x ^ A →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))

end Formalism.ZeroFreeDirichlet
