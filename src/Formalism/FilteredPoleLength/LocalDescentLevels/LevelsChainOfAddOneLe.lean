module

public import Mathlib
public import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
public import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0002
public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0005
public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0004

@[expose] public section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem levelsChain_of_add_one_le (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T : ℕ) (e : ℤ)
    (hep : ∀ z, 1 ≤ ep z) (hT : 1 ≤ T) (hc : 0 ≤ c') (hv : ∀ z, 0 ≤ v z)
    (hν : ∀ z, ν z ≤ νs + c' * v z) (he : (T : ℝ) * νs + 1 ≤ e) :
    ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hf : (0 : ℝ) ≤ f z := Nat.cast_nonneg _
  have hep0 : (1 : ℝ) ≤ ep z := by exact_mod_cast hep z
  have hT0 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hbound : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) ≤ (ep z : ℝ) * T * c' * v z := by
    have hy : 0 ≤ (ep z : ℝ) * T * c' * v z := by
      have := hv z
      positivity
    rw [Int.cast_max, Int.cast_zero]
    apply max_le hy
    have h1 := mul_le_mul_of_nonneg_left (hν z) (by linarith : (0 : ℝ) ≤ T)
    have h2 : (T : ℝ) * ν z - e ≤ T * c' * v z - 1 := by nlinarith
    have h3 : (ep z : ℝ) * ((T : ℝ) * ν z - e) ≤ (ep z) * (T * c' * v z - 1) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 := Int.ceil_lt_add_one ((ep z : ℝ) * ((T : ℝ) * ν z - e))
    nlinarith
  calc ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z
      ≤ (ep z : ℝ) * T * c' * v z * f z := mul_le_mul_of_nonneg_right hbound hf
    _ = T * c' * (((ep z : ℝ) * f z) * v z) := by ring

end Formalism.LatticeBaseChangeAlt
