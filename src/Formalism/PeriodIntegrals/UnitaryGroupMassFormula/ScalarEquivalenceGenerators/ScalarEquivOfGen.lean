module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0024

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.ScalPairs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_VS (D : D7) : finrank D.host.E (VS D).V = D.R.k + 2 * D.R.rS + 1 := by
  have h1 := (VS D).rank_eq
  have h2 : (VS D).rank = D.R.rankY 0 := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  rw [h1, h2]
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, zero_mul, add_zero]
  omega

theorem tu_ne_zero (D : D7) (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
  rw [Ne, Nat.cast_eq_zero]
  exact (D.mem u).A.T_prime.ne_zero

end PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace
