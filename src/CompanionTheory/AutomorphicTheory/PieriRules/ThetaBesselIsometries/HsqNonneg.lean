module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentClosureStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  show 0 ≤ max 1 T * b ^ (20 * (r + 1))
  have h1 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  have h2 : 0 ≤ b ^ (20 * (r + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (by positivity) _
  exact mul_nonneg h1 h2

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have he0 : e ≠ 0 := ne_of_gt he
  have hsq : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  have hprod : (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by
    field_simp <;> ring
  have key : (a' * a * d / e) ^ 2 ≤ (Real.sqrt (A * A') ^ n) ^ 2 := by
    rw [hprod, hsq]
    exact mul_le_mul h h' (by positivity) (pow_nonneg hA n)
  have hl : 0 ≤ a' * a * d / e := by positivity
  have hr : 0 ≤ Real.sqrt (A * A') ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  calc a' * a * d / e = Real.sqrt ((a' * a * d / e) ^ 2) := (Real.sqrt_sq hl).symm
    _ ≤ Real.sqrt ((Real.sqrt (A * A') ^ n) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (A * A') ^ n := Real.sqrt_sq hr

end GlobalTheory.SupTau
