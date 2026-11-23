module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0002

@[expose] public section

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset

theorem length_average_bound : LemmaB'_avg := by
  intro k n S mult hS hm hn j
  have key : ∀ i : Fin k, ∑ w ∈ S, mult w * w i = ∑ w ∈ S, mult w * w j := by
    intro i
    apply Finset.sum_nbij' (fun w => w ∘ Equiv.swap i j) (fun w => w ∘ Equiv.swap i j)
    · intro w hw; exact hS _ w hw
    · intro w hw; exact hS _ w hw
    · intro w _; funext a; simp [Function.comp]
    · intro w _; funext a; simp [Function.comp]
    · intro w _; simp [hm]
  have : ∑ i : Fin k, ∑ w ∈ S, mult w * w i = k * ∑ w ∈ S, mult w * w j := by
    rw [Finset.sum_congr rfl (fun i _ => key i)]; simp
  rw [← this, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.mul_sum, hn w hw, mul_comm]

end Formalism.HermitianLattices.LocalLatticeBases
