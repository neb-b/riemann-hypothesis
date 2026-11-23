module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AutomorphicArithmetic.MeanSquareBounds.Thin
public import Development.AutomorphicArithmetic.MeanSquareBounds.Bundle0001
public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

@[expose] public section

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem gauss_sum_function_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = G0 χ y := by
  have hmax : ∀ n ∈ Icc 1 ⌊y⌋₊, max (y / n - 1) 0 = y / n - 1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hy : 0 ≤ y := by
      by_contra hc
      rw [Nat.floor_of_nonpos (le_of_lt (not_le.1 hc))] at h2
      omega
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy).1 h2
    have : 1 ≤ y / n := (one_le_div hn0).2 hny
    exact max_eq_left (by linarith)
  unfold Formalism.HC.An.gChi G0
  by_cases h : χ = 1
  · rw [if_pos h, if_pos h]
    unfold Formalism.HC.An.G G1
    rw [Finset.sum_congr rfl fun n hn => by rw [hmax n hn]]
  · rw [if_neg h, if_neg h]
    unfold Formalism.HC.An.sumLamChi Gchi Formalism.HC.An.logDerivativeAtOne logDerivLAtOne
    rw [Finset.sum_congr rfl fun n hn => by rw [hmax n hn]]

private theorem isReal_of_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.2 h2 a with h | h | h <;> simp [h]

end QH

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

end GlobalTheory.EX
