module

public import Mathlib
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP

@[expose] public section

open Finset ArithmeticFunction Classical

noncomputable section

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

def X1 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5))

def X2 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5) * Real.log x ^ 2)

def logDerivLAtOne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def Gchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * logDerivLAtOne χ

def G1 (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (y / n - 1)) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def cN (x : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (x / n)

def Sz {q : ℕ} (χ : DirichletCharacter ℂ q) (x z : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊z⌋₊, ((cN x n : ℝ) : ℂ) * χ (n : ZMod q)

def tailL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℝ) : ℂ :=
  - logDerivLAtOne χ - ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)

def qc (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

instance neZeroMulPrime {t q : ℕ} [NeZero t] [Fact q.Prime] : NeZero (t * q) :=
  ⟨Nat.mul_ne_zero (NeZero.ne t) (Fact.out : q.Prime).ne_zero⟩

def tw {t : ℕ} (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ (t * q) :=
  DirichletCharacter.changeLevel (Dvd.intro q rfl) θ * DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)

def ZeroFreeBox {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0

def GoodFor {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q χ

def PPset (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun q => q.Prime ∧ q % m₀ = a₀ % m₀ ∧ X ^ (1 / 2 : ℝ) < (q : ℝ))

def oddM (y : ℝ) (q₁ : ℕ) : ℕ := q₁ * ∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p

def IsNormOne (d N p : ℕ) : Prop :=
  ∃ u v : ℤ, (N : ℤ) ∣ u - 1 ∧ (N : ℤ) ∣ v ∧ (p : ℤ) = u ^ 2 + u * v + (((d + 1) / 4 : ℕ) : ℤ) * v ^ 2

def normPrimes (d N : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (Icc 1 ⌊hi⌋₊).filter (fun p => p.Prime ∧ lo < (p : ℝ) ∧ IsNormOne d N p)

def rho (c Cρ B X : ℝ) : ℝ :=
  Cρ * Real.exp (-c * Real.log X / Real.log B) + Cρ * Real.exp (-c * Real.log X ^ (1 / 2 : ℝ))

def BoxCountHyp (C : ℝ) : Prop :=
  ∀ (t : ℕ) [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (S : Finset ℕ), θ.IsPrimitive → θ ^ 2 = 1 →
    (∀ q ∈ S, ∃ _ : Fact q.Prime, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBox Q (tw θ q)) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

def BoxTailHyp (ε C x₀ : ℝ) : Prop :=
  ∀ (x Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), x₀ ≤ x → x ^ (ε / 6) ≤ Real.log Q →
    Real.log Q ≤ x ^ (ε / 4) → χ ≠ 1 → GoodFor Q χ →
    ‖(x : ℂ) * tailL χ (x ^ 400)‖ ≤ x ^ ε ∧ ‖logDerivLAtOne χ‖ ≤ C * Real.log x

def IntervalHyp (C₀ c Cρ c₃ : ℝ) : Prop :=
  ∀ (d N : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 1 ≤ N → (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ C₀ ≤ X →
    rho c Cρ (4 * (d : ℝ) * (N : ℝ) ^ 2) X ≤ h / 100 → 0 < h → h ≤ 1 →
    (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ 7 ≤ h * X ^ (1 / 3 : ℝ) →
    c₃ * h * (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d N X (X * (1 + h))).card : ℝ)

def GFiniteSplit : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x z : ℝ), 0 < x → x ≤ z →
    Gchi χ x = - Sz χ x z - (x : ℂ) * tailL χ z

def UnitModulusIncrementConditions : Prop :=
  ∀ ε C : ℝ, 0 < ε → ε ≤ 1 → 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    x ^ 400 < X1 ε x ^ (1 / 2 : ℝ) ∧ 2 ≤ x ^ (ε / 5) ∧
    (1 / 4) * Real.log x ^ 2 * Real.log 8 ≤ Real.log (X1 ε x) ∧
    Real.log x ^ 2 * Real.log (8 * (x ^ 400) ^ 2) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (8 * X1 ε x) ∧ Real.log (8 * X1 ε x) ≤ x ^ (ε / 4) ∧
    C * x * Real.log x / (x ^ (1 / 2 + ε) / 2) ^ 2 ≤ x ^ (-ε) ∧ x ^ (-ε) ≤ 1 / 8 ∧
    2 * (C * (8 * X1 ε x) ^ (1 / 4 : ℝ)) ≤ X1 ε x ^ (9 / 10 : ℝ) / 2

def TwEval : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] (n : ℕ),
    tw θ q (n : ZMod (t * q)) = θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

def TwPrimitive : Prop :=
  (chi8.IsPrimitive ∧ chi8 ^ 2 = 1) ∧
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime], θ.IsPrimitive → q ≠ 2 → q.Coprime t →
    (tw θ q).IsPrimitive ∧ tw θ q ≠ 1 ∧ (θ ^ 2 = 1 → tw θ q ^ 2 = 1)

def SmoothingSizeBounds : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y lam : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → 0 < lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    x ^ (ε / 3) / 2 ≤ Real.log y ∧ x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) ≤ Real.log y / lam ∧
    x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y)

def ThinIntegral : Prop :=
  ∀ ε c : ℝ, 0 < ε → 0 < c → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ V lam : ℝ, x ^ (ε / 3) / 2 ≤ V → 1 ≤ lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    MeasureTheory.IntegrableOn (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) ∧
    (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤ Real.exp (-c' * x ^ (ε / 8))

def TailIntegralBoundOfPsiBound : Prop :=
  ∀ ε c C : ℝ, 0 < ε → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (y lam : ℝ) (psi0 : ℝ → ℂ),
    Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ u : ℝ, y ≤ u → ‖psi0 u‖ ≤
      C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
    ‖(y : ℂ) * ∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ y * Real.exp (-c' * x ^ (ε / 8))

end Formalism.HermitianLattices.ZeroFreeRegionGL2
