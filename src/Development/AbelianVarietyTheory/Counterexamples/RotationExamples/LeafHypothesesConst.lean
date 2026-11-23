module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.L2.Indef Formalism.L2.Indef.Tree

noncomputable section

namespace GlobalTheory.LeafRestExamples

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

def truncZero (y : ℝ) : ℤ := if 0 ≤ y then ⌊y⌋ else ⌈y⌉

theorem abs_truncZero_le (y : ℝ) (a : ℤ) :
    |(truncZero y : ℝ)| ≤ |y| ∧ |((a + truncZero y : ℤ) : ℝ)| ≤ |(a : ℝ) + y| + |y| := by
  have key : |(truncZero y : ℝ)| ≤ |y| ∧ |(truncZero y : ℝ) - y| ≤ |y| := by
    unfold truncZero
    split_ifs with h
    · have h1 := Int.floor_le y
      have h2 : (0 : ℝ) ≤ (⌊y⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.mpr h
      rw [abs_of_nonneg h, abs_of_nonneg h2, abs_of_nonpos (by linarith)]
      constructor <;> linarith
    · push Not at h
      have h1 := Int.le_ceil y
      have h2 : ((⌈y⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_nonpos.mpr h.le
      rw [abs_of_neg h, abs_of_nonpos h2, abs_of_nonneg (by linarith)]
      constructor <;> linarith
  refine ⟨key.1, ?_⟩
  push_cast
  calc |(a : ℝ) + truncZero y| = |((a : ℝ) + y) + (truncZero y - y)| := by ring_nf
    _ ≤ |(a : ℝ) + y| + |(truncZero y : ℝ) - y| := abs_add_le _ _
    _ ≤ _ := by linarith [key.2]

end GlobalTheory.LeafRestExamples
