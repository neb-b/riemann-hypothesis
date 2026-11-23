module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004

@[expose] public section

noncomputable section

namespace GlobalTheory.HopfOrderCheck

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem vdet_le_of_span_le (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det ≤ v B'.det := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => B' x i) = fun x => B x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).mp (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  have hB : B = B' * (Matrix.of fun i j => c j i).map (algebraMap R C) := by
    ext x j
    have := congrFun (hc j) x
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hd : ((Matrix.of fun i j => c j i).map (algebraMap R C)).det
      = algebraMap R C (Matrix.of fun i j => c j i).det := ((algebraMap R C).map_det _).symm
  rw [hB, Matrix.det_mul, map_mul, hd]
  exact mul_le_of_le_one_right' (hv _)

theorem hasColen_unique (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)} {c c' : NNReal}
    (h : HasColen R v M c) (h' : HasColen R v M c') : c = c' := by
  obtain ⟨B, hB, rfl⟩ := h
  obtain ⟨B', hB', rfl⟩ := h'
  exact le_antisymm (vdet_le_of_span_le v hv B B' (by rw [← hB, ← hB']))
    (vdet_le_of_span_le v hv B' B (by rw [← hB, ← hB']))

end GlobalTheory.HopfOrderCheck
