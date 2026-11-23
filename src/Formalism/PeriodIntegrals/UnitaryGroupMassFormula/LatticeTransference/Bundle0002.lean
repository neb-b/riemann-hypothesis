module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.GaussAbs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.TransferenceKey

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall
section
open Module

namespace PI.Tr

private theorem exists_generator_of_finrank_eq_one_zLattice {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h1 : finrank ℝ E = 1) :
    ∃ a ∈ Λ, a ≠ 0 ∧ ∀ x ∈ Λ, ∃ k : ℤ, x = (k : ℝ) • a := by
  have hrk : finrank ℤ Λ = 1 := (ZLattice.rank ℝ Λ).trans h1
  let b := Module.finBasisOfFinrankEq ℤ Λ hrk
  refine ⟨(b 0 : E), (b 0).2, fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩
  intro x hx
  refine ⟨b.repr ⟨x, hx⟩ 0, ?_⟩
  have h2 : ((b.repr ⟨x, hx⟩ 0 • b 0 : Λ) : E) = x := by
    have hs := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at hs
    rw [hs]
  rw [Int.cast_smul_eq_zsmul]
  exact h2.symm.trans (Submodule.coe_smul _ _)

theorem keySmall : KeySmall := by
  intro E _ _ _ Λ _ _ lam u hdim hlam hdual
  have hdim' : finrank ℝ E ≤ 1 := hdim
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdim' with h0 | h1
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    refine ⟨0, Λ.zero_mem, ?_⟩
    rw [Subsingleton.elim u 0, h0]
    simp
  · obtain ⟨a, haΛ, ha0, hmul⟩ := exists_generator_of_finrank_eq_one_zLattice Λ h1
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, u = t • a := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' a ha0).mp h1 u
      exact ⟨c, hc.symm⟩
    have hα : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    rw [h1, Nat.cast_one]
    by_cases hc : lam * ‖a‖ ≤ 1
    · refine ⟨((round t : ℤ) : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        calc |t - ((round t : ℤ) : ℝ)| * ‖a‖ * lam ≤ (1 / 2) * ‖a‖ * lam :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (abs_sub_round t) (norm_nonneg a)) hlam.le
          _ = (1 / 2) * (lam * ‖a‖) := by ring
          _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hc (by norm_num)
          _ = 1 / 2 := by ring
    · push Not at hc
      have hα2 : ‖a‖ ^ 2 ≠ 0 := by positivity
      have key : ∀ s : ℝ, inner ℝ (s • a) ((‖a‖ ^ 2)⁻¹ • a) = s := by
        intro s
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
          inv_mul_cancel₀ hα2, mul_one]
      have hnorm : ‖(‖a‖ ^ 2)⁻¹ • a‖ < lam := by
        rw [norm_smul, norm_inv, norm_pow, norm_norm]
        have e : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ = 1 := by
          rw [mul_assoc, ← sq, inv_mul_cancel₀ hα2]
        have hlt : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ < lam * ‖a‖ := by
          rw [e]
          exact hc
        exact lt_of_mul_lt_mul_right hlt hα.le
      obtain ⟨m, hm⟩ := hdual ((‖a‖ ^ 2)⁻¹ • a)
        (by
          intro x hx
          obtain ⟨k, rfl⟩ := hmul x hx
          exact ⟨k, key _⟩) hnorm
      rw [key] at hm
      refine ⟨(m : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [hm, sub_self, norm_zero, zero_mul]
        norm_num

end PI.Tr
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.NumericMain
section
open Module
open scoped Real

namespace PI.Tr

theorem numeric_main : 9 / 4 * Real.exp (-(2 * π / 5)) + 2 * (4 * Real.exp (-(25 * π / 24))) < 1 := by
  have hpi := Real.pi_gt_d2
  have e1 := Real.exp_one_gt_d9
  have q1 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.256 by norm_num)
  have q2 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.27 by norm_num)
  have p1 := Real.exp_pos 0.256
  have p2 := Real.exp_pos 0.27
  have hX : 3.5 < Real.exp (2 * π / 5) := by
    have h : Real.exp 1.256 ≤ Real.exp (2 * π / 5) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 1.256 = Real.exp 1 * Real.exp 0.256 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hY : 26 < Real.exp (25 * π / 24) := by
    have h : Real.exp 3.27 ≤ Real.exp (25 * π / 24) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 3.27 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 0.27 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
    have e3 : 20 < Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
    nlinarith
  have hXp : 0 < Real.exp (2 * π / 5) := Real.exp_pos _
  have hYp : 0 < Real.exp (25 * π / 24) := Real.exp_pos _
  rw [Real.exp_neg, Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
  have ha : 1 / Real.exp (2 * π / 5) < 2 / 7 := by
    rw [div_lt_iff₀ hXp]; linarith
  have hb : 1 / Real.exp (25 * π / 24) < 1 / 26 := by
    rw [div_lt_iff₀ hYp]; linarith
  linarith

theorem factor_le (κ τ m : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m) (hh : τ⁻¹ * Real.exp (-κ) ≤ 1) :
    Real.exp (-κ * m) * τ ^ (-m) ≤ τ⁻¹ * Real.exp (-κ) := by
  have hb : 0 < τ⁻¹ * Real.exp (-κ) := by positivity
  have key : Real.exp (-κ * m) * τ ^ (-m) = (τ⁻¹ * Real.exp (-κ)) ^ m := by
    rw [Real.mul_rpow (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le, Real.inv_rpow hτ.le,
      ← Real.rpow_neg hτ.le, ← Real.exp_mul]
    ring
  rw [key]
  calc (τ⁻¹ * Real.exp (-κ)) ^ m ≤ (τ⁻¹ * Real.exp (-κ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hb hh hm
    _ = τ⁻¹ * Real.exp (-κ) := Real.rpow_one _

theorem gaussStep : GaussStep := by
  intro hP E _ _ _ Λ _ _ lam u hn hlam hdual
  obtain ⟨sA, sQ, c, hc, PE⟩ := hP E Λ
  by_contra hcon
  push_neg at hcon
  set n : ℝ := (finrank ℝ E : ℝ) with hndef
  have hn2 : (2 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  set m : ℝ := n / 2 with hmdef
  have hm1 : 1 ≤ m := by rw [hmdef]; linarith
  have hm0 : 0 < m := by linarith
  set R2 : ℝ := (m / lam) ^ 2 with hR2
  set s : ℝ := 18 / 25 * lam ^ 2 / m with hsdef
  have hs : 0 < s := by positivity
  have hR : ∀ x : Λ, R2 ≤ ‖(x : E) + -u‖ ^ 2 := by
    intro x
    have h := hcon x x.2
    have h' : m / lam < ‖(x : E) + -u‖ := by
      rw [div_lt_iff₀ hlam, ← sub_eq_add_neg, norm_sub_rev]
      rw [hmdef]; linarith
    rw [hR2]
    exact pow_le_pow_left₀ (by positivity) h'.le 2
  have hl : ∀ y : dualLat Λ, ‖(y : E)‖ ^ 2 < lam ^ 2 →
      Real.cos (2 * π * inner ℝ (y : E) (-u)) = 1 := by
    intro y hy
    have hy' : ‖(y : E)‖ < lam := by
      nlinarith [norm_nonneg (y : E)]
    obtain ⟨k, hk⟩ := hdual y (fun x hx => y.2 x hx) hy'
    rw [inner_neg_right, real_inner_comm, hk]
    have : 2 * π * -(k : ℝ) = ((-k : ℤ) : ℝ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_int_mul_two_pi]
  have key := gauss_abstract (X := Λ) (Y := dualLat Λ) (fun x => ‖(x : E) + -u‖ ^ 2)
    (fun x => ‖(x : E) + 0‖ ^ 2) (fun y => ‖(y : E)‖ ^ 2)
    (fun y => Real.cos (2 * π * inner ℝ (y : E) (-u))) n c
    (fun y => sq_nonneg _) (fun x => sq_nonneg _) (fun y => Real.abs_cos_le_one _) hc 0
    (fun t ht => sA t ht (-u)) (fun t ht => sA t ht 0) (fun t ht => sQ t ht)
    (fun t ht => PE t ht (-u))
    (fun t ht => by
      rw [PE t ht 0]
      simp only [inner_zero_right, mul_zero, Real.cos_zero, mul_one])
    R2 (lam ^ 2) hR hl s (4 / 9) (1 / 4) hs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hm0' : m ≠ 0 := hm0.ne'
  have e1 : -π * s * (1 - 4 / 9) * R2 = -(2 * π / 5) * m := by
    rw [hsdef, hR2]; field_simp; ring
  have e2 : -π * (1 - 1 / 4) * lam ^ 2 / s = -(25 * π / 24) * m := by
    rw [hsdef]; field_simp; ring
  have e3 : -n / 2 = -m := by rw [hmdef]; ring
  rw [e1, e2, e3] at key
  have hN := numeric_main
  have hA : 0 < Real.exp (-(2 * π / 5)) := Real.exp_pos _
  have hB : 0 < Real.exp (-(25 * π / 24)) := Real.exp_pos _
  have f1 := factor_le (2 * π / 5) (4 / 9) m (by norm_num) hm1 (by
    rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]; linarith)
  have f2 := factor_le (25 * π / 24) (1 / 4) m (by norm_num) hm1 (by
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]; linarith)
  rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num] at f1
  rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at f2
  linarith

end PI.Tr
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton
section
open Module

namespace PI.Tr

theorem key_of (hL : KeyLarge) (hS : KeySmall) : PI.TransferenceKey := by
  intro E _ _ _ Λ _ _ lam u hlam hu
  rcases Nat.lt_or_ge (finrank ℝ E) 2 with h | h
  · exact hS E Λ lam u (by omega) hlam hu
  · exact hL E Λ lam u h hlam hu

theorem transferenceCover_of' (hP : PoissonGauss) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceCover := PI.cover_of_key (key_of (hG hP) hS)

theorem transferenceMinima_of' (hP : PoissonGauss) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceMinima := PI.minima_of_key (key_of (hG hP) hS)

end PI.Tr
end

