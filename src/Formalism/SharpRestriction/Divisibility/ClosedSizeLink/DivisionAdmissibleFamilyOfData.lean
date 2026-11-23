module

public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.AdmissibleParameterJoins
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

section One

variable {D : D7} (L : SizeData₂ D)

theorem prod_gTypes : (∏ g ∈ L.gTypes, (g : ℝ)) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by
  unfold SizeData₂.gTypes
  rw [Finset.prod_pair D.host.g_ne]

theorem x_pos : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (x_pos L).le _)

theorem one_le_a : 1 ≤ L.sc.a := by
  unfold Scale.a
  have h1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have h2 := one_le_b L
  nlinarith

theorem La_nonneg (hS : SizeQD L) : 0 ≤ L.La := by
  unfold SizeData₂.La
  have h1 := one_le_a L
  have h2 : 1 ≤ D.host.rdE := hS.2.2.2.2.2.2.1
  exact Real.log_nonneg (by nlinarith)

end One

section Mono

variable {D : D7} (L : SizeData₂ D)

end Mono

section Link

variable {eps : ℝ} (Fm : FamP eps)

end Link

end Formalism.MainNotions.DIV

end
