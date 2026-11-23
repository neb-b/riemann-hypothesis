module

public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0006
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPairs
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0004
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def cZ : ℝ := min (Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet) (1 / 20)

def eOf (M : ℕ) [NeZero M] : Option (DirichletCharacter ℂ M × ℝ) :=
  if h : ∃ p : DirichletCharacter ℂ M × ℝ, IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ) then some h.choose
  else if h' : ∃ p : DirichletCharacter ℂ M × ℝ, IsExcPair p.1 p.2 then some h'.choose else none

def etaOf (M : ℕ) [NeZero M] : ℝ :=
  match eOf M with
  | none => 1
  | some (_, β₁) => min 1 ((1 - β₁) * Real.log M)

def mainPsi {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  (if χ = 1 then (y : ℂ) else 0) -
    (match e with
     | none => 0
     | some (χ₁, β₁) => if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0)

def excW {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) : ℕ :=
  match e with
  | none => 0
  | some (χ₁, β₁) => if χ = χ₁ ∧ ρ = (β₁ : ℂ) then 1 else 0

def PsiRel : Prop :=
  ∃ c A C₀ : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))

def PsiRelA : Prop :=
  ∃ cA c A : ℝ, 0 < cA ∧ 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    Real.log M ≤ cA * Real.sqrt (Real.log y) →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * Real.exp (-(c * Real.sqrt (Real.log y)))

def PsiRelB (cA : ℝ) : Prop :=
  ∃ c A C₀ : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y → cA * Real.sqrt (Real.log y) < Real.log M →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * Real.exp (-(c * Real.log y / Real.log M))

def ExplicitS : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 20 → ∃ C : ℝ, 0 < C ∧
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 2 ≤ T →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (K : ℂ),
      (∀ ρ ∈ Z, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ T + 1) ∧
      (∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∀ t : ℝ, ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), m ρ : ℕ) : ℝ) ≤
        C * Real.log ((M : ℝ) * (|t| + 2))) ∧
      ∀ y : ℝ, 2 ≤ y →
        ‖Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                  ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
          C * (((M : ℝ) * T) ^ C * y ^ (-(κ / 2)) + Real.log y * Real.log ((M : ℝ) * T) ^ 2 / T)

def SharpenS : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (Z : Finset ℂ) (m : ℂ → ℕ) (K : ℂ) (E y δ : ℝ),
    (∀ ρ ∈ Z, 1 / 2 ≤ ρ.re ∧ ρ.re < 1) → 2 ≤ y → 0 < δ → δ ≤ 1 / 2 →
    (∀ u : ℝ, (u = y ∨ u = (1 + δ) * y) →
      ‖Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - K - (if χ = 1 then ((Real.log u - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (u : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤ E) →
    ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) + 4 * (δ * y + 1) * Real.log (2 * y)

def LogDensityM : Prop :=
  ∃ A B C : ℝ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 1 / 2 ≤ σ →
    (∀ p ∈ S, σ ≤ p.2.re ∧ |p.2.im| ≤ T ∧ IsLZero p.1 p.2) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((M : ℝ) * T) ^ B

def ZeroSum : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 20 ∧ ∀ C₁ A₁ : ℝ, 1 ≤ A₁ → ∃ c A C₀ : ℝ, 0 < c ∧
    ∀ (M : ℕ) [NeZero M] (Z : DirichletCharacter ℂ M → Finset ℂ) (m : DirichletCharacter ℂ M → ℂ → ℕ),
    8 ∣ M →
    (∀ χ, ∀ ρ ∈ Z χ, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ (M : ℝ) ^ A₁ + 1) →
    (∀ χ, ∀ ρ ∈ Z χ, 1 ≤ m χ ρ) →
    (∀ χ, ∀ ρ ∈ Z χ, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m χ ρ = 1) →
    (∀ χ, ∀ t : ℝ, ((∑ ρ ∈ (Z χ).filter (fun ρ => |ρ.im - t| ≤ 1), m χ ρ : ℕ) : ℝ) ≤
      C₁ * Real.log ((M : ℝ) * (|t| + 2))) →
    ∀ y : ℝ, 2 ≤ y → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤
        A * etaOf M * Real.exp (-(c * Real.log y / Real.log M))

def GlueOf : Prop := PsiRelA → (∀ cA : ℝ, 0 < cA → PsiRelB cA) → PsiRel

def PiOf : Prop := PsiRel → PNTAPRelW

def PsiRelBOf : Prop := ExplicitS → SharpenS → ZeroSum → ∀ cA : ℝ, 0 < cA → PsiRelB cA

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMain
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem cN_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n := by
  unfold cN
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))

theorem cN_primePow (x : ℝ) (n : ℕ) (h : cN x n ≠ 0) : IsPrimePow n := by
  unfold cN at h
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)

theorem RR_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N :=
  Finset.sum_nonneg fun n _ => hc n

theorem abs_sum_jacobi_le (PP : Finset ℕ) (s : ℕ) :
    |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ (PP.card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PP, |(jacobiSym (q : ℤ) s : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy (q : ℤ) s with h | h | h <;> simp [h]
  simpa using Finset.sum_le_sum this

theorem abs_pair_sum_eq (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hn : 0 < n)
    (hn' : 0 < n') (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
  obtain ⟨σ, hσ, h⟩ := jacobi_class m₀ a₀ (n * n') h8 ha (Nat.mul_pos hn hn')
  have h1 : ∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ) =
      (σ : ℝ) * ∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hp, hm, hlt⟩ := hPP q hq
    have := h q hp hm hlt
    rw [← jacobiSym.mul_left, ← Int.cast_mul, ← this]
    push_cast
    rfl
  rw [h1, abs_mul]
  rcases hσ with h | h <;> simp [h]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

