module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderSignIdentity.SkipOneEqSuccAbove
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.IsCompactInterUnitBox
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGGenRatio
section
theorem generic_ratio_bound : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := by
  unfold Formalism.L2.SG.GGMirabolic.GenericRatioOfBound
  intro hMir hCard
  unfold Formalism.L2.SG.GGMirabolic.GenericRatio
  intro F _ _ k ψ₀ hψ V _ _ _ π hirr hgen
  have hb := hMir F k ψ₀ hψ V π hirr hgen
  rw [hCard F k]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i := by
    intro i hi
    have hi1 : i ≠ 0 := by
      simp only [Finset.mem_Ico] at hi
      omega
    exact one_lt_pow₀ hqR hi1
  have hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2 := by
    rw [← Finset.sum_range_id]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
      simp
  have hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) :=
    Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)
  have hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ) := by
    rw [← hcast]
    exact_mod_cast hb
  have hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
      = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have h1 := hx i hi
    have h0 : (Fintype.card F : ℝ) ^ i ≠ 0 := (lt_trans one_pos h1).ne'
    have h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0 := (sub_pos.mpr h1).ne'
    field_simp
  rw [hR, Nat.cast_pow]
  gcongr
  all_goals first
    | exact hPD
    | exact hP.le
    | exact hP
    | positivity
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderES
section
theorem quantum_minor_border_es : PI.QmBorderES := PI.UnitaryGroupMassFormula.QmBorderES.qmBorderES_of quantum_minor_column_expansion quantum_minor_row_expansion
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
section
open PI.QuotSetU.UnitaryGroupMassFormula in
theorem quotient_measure_unitary_group : PI.QuotSetU :=
  quotSetU_of unitary_hermitian_group siegel_set_subset (SW.sGroup_of unitary_weyl_compact) exists_modular_function unitary_group_modular_function_trivial
    (SW.trivS_of (SW.sGroup_of unitary_weyl_compact) unitary_weyl_compact SW.nilpotent_subgroup SW.unipotent_radical_contracting)
end

