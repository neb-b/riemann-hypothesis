module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectIntEqZeroOfDifferentiableOn

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing
section
noncomputable section

namespace PI.EF

open Complex

theorem fractionFieldToGenericStalk_algebraMap_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : ℝ) :
    psi0 χ u = psiRaw χ u - del1 χ * u := by
  unfold psi0 psiRaw del1
  split_ifs <;> simp

theorem first_character_sum_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 ≤ S1 χ := by
  unfold S1
  exact finsum_nonneg (fun ρ => finsum_nonneg (fun _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem explicitFormula_of_perron_shift (κ : ℝ) (h1 : ∃ C, 0 < C ∧ PerronL C)
    (h2 : ∃ C, 0 < C ∧ ShiftBound κ C) (h3 : GoodHeightExists κ)
    (h4 : ∃ C, 0 < C ∧ TruncChange C) (h5 : ZerosFinite) : PI.ExplicitFormula := by
  obtain ⟨C1, hC1, H1⟩ := h1
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C4, hC4, H4⟩ := h4
  refine ⟨C1 + C2 + C4, by positivity, ?_⟩
  intro N _ χ hχ u T hT hTu
  refine ⟨h5 N χ hχ T, ?_⟩
  obtain ⟨T', hT1, hT2, hg⟩ := h3 N χ hχ T hT
  have e1 := H1 N χ u T T' hT hTu hT1 hT2
  have e2 := H2 N χ hχ u T T' hT hTu hT1 hT2 hg
  have e4 := H4 N χ hχ u T T' hT hTu hT1 hT2
  have hS : 0 ≤ S1 χ := first_character_sum_nonneg χ
  have key : psi0 χ u + zsum χ T u = (psiRaw χ u - vertInt χ u T') +
      (vertInt χ u T' - del1 χ * u + zsum χ T' u) - (zsum χ T' u - zsum χ T u) := by
    rw [fractionFieldToGenericStalk_algebraMap_eq]; ring
  show ‖psi0 χ u + zsum χ T u‖ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ)
  rw [key]
  calc ‖(psiRaw χ u - vertInt χ u T') + (vertInt χ u T' - del1 χ * u + zsum χ T' u) -
        (zsum χ T' u - zsum χ T u)‖
      ≤ ‖psiRaw χ u - vertInt χ u T'‖ + ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ +
        ‖zsum χ T' u - zsum χ T u‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ C1 * Err N u T + C2 * (Err N u T + S1 χ) + C4 * Err N u T := by gcongr
    _ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hC1.le hS, mul_nonneg hC4.le hS]

def GlueLocalLemma : Prop :=
  LocalAbstract → (∃ A C, 0 < A ∧ 0 < C ∧ LGrowth A C) → ZeroLocus → PI.ZerosWindow →
    ∃ C, 0 < C ∧ LocalLemma C

def GlueContour : Prop := RectResidue → ZeroLocus → ZerosFinite → ContourIdentity

def GlueSides : Prop :=
  ∀ κ, 0 < κ → (∃ C, 0 < C ∧ LogDerivHoriz κ C) → (∃ C, 0 < C ∧ LogDerivLeft C) →
    ∃ C, 0 < C ∧ SidesBound κ C

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthMain
section
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N]

theorem L_right (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 8) :
    ‖LFunction χ w‖ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by
  have hre : 0 < w.re := by linarith
  have hb := hB N χ hχ1 w hre
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg w.im
  have hw : ‖w‖ ≤ 8 + |w.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hq : ‖w‖ / w.re ≤ 2 * (8 + |w.im|) := by
    rw [div_le_iff₀ hre]
    nlinarith [norm_nonneg w]
  calc ‖LFunction χ w‖ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + ‖w‖ / w.re) := hb
    _ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 2 * (8 + |w.im|)) := by gcongr
    _ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by nlinarith

theorem L_nontriv_growth (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg s.im
  have hX : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := one_le_mul_of_one_le_of_one_le hN (by linarith)
  by_cases hr : 1 / 2 ≤ s.re
  · calc ‖LFunction χ s‖ ≤ 37 * ((N : ℝ) * (|s.im| + 2)) := L_right hB hχ1 hr h2
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
        have : (N : ℝ) * (|s.im| + 2) ≤ ((N : ℝ) * (|s.im| + 2)) ^ 7 := le_self_pow₀ hX (by norm_num)
        nlinarith
  · push_neg at hr
    have h0 : χ 0 = 0 := by
      by_cases hN1 : N = 1
      · subst hN1
        exfalso
        apply hχ1
        exact MulChar.ext fun a => by rw [Subsingleton.elim a 1]; simp
      · haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1
        exact χ.map_nonunit not_isUnit_zero
    have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hL1 := norm_L_one_sub_le hχ hw1 hw2 (Or.inl h0)
    rw [sub_sub_cancel] at hL1
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ1
    have hL2 := L_right hB hinv hw1 (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have hwim : |(1 - s).im| = |s.im| := by simp
    rw [hwim] at hL2
    have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e : |(1 - s + 1).im| = |s.im| := by simp
      have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
      rw [e, e2, abs_of_pos (by linarith)]
      linarith
    calc ‖LFunction χ s‖ ≤ 6 * (N : ℝ) ^ 5 * ‖1 - s + 1‖ ^ 5 * ‖LFunction χ⁻¹ (1 - s)‖ := hL1
      _ ≤ 6 * (N : ℝ) ^ 5 * (6 + |s.im|) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by gcongr
      _ ≤ 6 * (N : ℝ) ^ 5 * (3 * (|s.im| + 2)) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by
          gcongr
          linarith
      _ = 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 6 := by ring
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by norm_num)) (by norm_num)

theorem lGrowth_of (hB : PI.LBoundRight) {C : ℝ} (hZ : ZetaGrowth C) :
    LGrowth 7 (max C 53946) := by
  intro N _ χ hχ s h1 h2
  have e7 : ∀ x : ℝ, x ^ (7 : ℝ) = x ^ (7 : ℕ) := fun x => by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e7]
  by_cases hc : χ = 1
  · subst hc
    have hN : N = 1 := by
      have h0 := hχ
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at h0
      exact h0.symm
    subst hN
    simp only [del1, ↓reduceIte, one_mul]
    rw [show (1 : ℂ) + (s - 2) = s - 1 by ring, DirichletCharacter.LFunction_modOne_eq]
    refine le_trans (hZ s h1 h2) ?_
    simp only [Nat.cast_one, one_mul]
    gcongr
    exact le_max_left _ _
  · simp only [del1, hc, ↓reduceIte, zero_mul, add_zero, one_mul]
    calc ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := L_nontriv_growth hB hχ hc h1 h2
      _ ≤ max C 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
          gcongr
          exact le_max_right _ _

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthZeta
section
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem zeta_one_sub_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : w ≠ 1) :
    ‖riemannZeta (1 - w)‖ ≤ 6 * ‖w + 1‖ ^ 5 * ‖riemannZeta w‖ := by
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have h0 := norm_L_one_sub_le (N := 1) hp h1 h2 (Or.inr h)
  simpa [DirichletCharacter.LFunction_modOne_eq] using h0

theorem zeta_right (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := by
  by_cases hs : s = 1
  · subst hs
    simp only [sub_self, zero_mul, norm_zero]
    positivity
  have hre : 0 < s.re := by linarith
  have hb := hZ s hre hs
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs)
  have ht := abs_nonneg s.im
  have hs_le : ‖s‖ ≤ 8 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hs1_le : ‖s - 1‖ ≤ 7 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |s.re - 1| ≤ 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hinv : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hre]; linarith
  rw [norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖s - 1‖ + 1 + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
        rw [mul_add, mul_add, mul_one_div_cancel hn1.ne']
        ring
    _ ≤ (7 + |s.im|) + 1 + (7 + |s.im|) * (8 + |s.im|) * (1 + 2) := by gcongr
    _ ≤ 51 * (|s.im| + 2) ^ 2 := by nlinarith

theorem zeta_left (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re < 1 / 2)
    (h3 : 1 / 2 ≤ ‖s‖) : ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h3
    norm_num at h3
  have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw : (1 - s) ≠ 1 := by
    intro h0
    apply hs0
    linear_combination -h0
  have hz1 := zeta_one_sub_le hw1 hw2 hw
  rw [sub_sub_cancel] at hz1
  have hwre : 0 < (1 - s).re := by linarith
  have hz2 := hZ (1 - s) hwre hw
  have ht := abs_nonneg s.im
  have hwim : |(1 - s).im| = |s.im| := by simp
  have hn : ‖1 - s - 1‖ = ‖s‖ := by rw [show 1 - s - 1 = -s by ring, norm_neg]
  have hinv1 : 1 / ‖1 - s - 1‖ ≤ 2 := by
    rw [hn, div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : 1 / (1 - s).re ≤ 2 := by rw [div_le_iff₀ hwre]; linarith
  have hw_le : ‖1 - s‖ ≤ 5 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hwim, abs_of_pos hwre]
    linarith
  have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e : |(1 - s + 1).im| = |s.im| := by simp
    have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
    rw [e, e2, abs_of_pos (by linarith)]
    linarith
  have hzw : ‖riemannZeta (1 - s)‖ ≤ 18 + 3 * |s.im| := by
    calc ‖riemannZeta (1 - s)‖ ≤ 1 + 1 / ‖1 - s - 1‖ + ‖1 - s‖ * (1 + 1 / (1 - s).re) := hz2
      _ ≤ 1 + 2 + (5 + |s.im|) * (1 + 2) := by gcongr
      _ = 18 + 3 * |s.im| := by ring
  have hsn : ‖s - 1‖ = ‖1 - s‖ := norm_sub_rev _ _
  rw [norm_mul, hsn]
  calc ‖1 - s‖ * ‖riemannZeta s‖ ≤ ‖1 - s‖ * (6 * ‖1 - s + 1‖ ^ 5 * ‖riemannZeta (1 - s)‖) := by gcongr
    _ ≤ (5 + |s.im|) * (6 * (6 + |s.im|) ^ 5 * (18 + 3 * |s.im|)) := by gcongr
    _ ≤ (3 * (|s.im| + 2)) * (6 * (3 * (|s.im| + 2)) ^ 5 * (9 * (|s.im| + 2))) := by
        gcongr <;> linarith
    _ = 39366 * (|s.im| + 2) ^ 7 := by ring
    _ ≤ 48114 * (|s.im| + 2) ^ 7 := by gcongr; norm_num

theorem zetaGrowth_of (hZ : PI.ZetaBoundRight) : ZetaGrowth 300000 := by
  intro s hs1 hs2
  have ht := abs_nonneg s.im
  have h2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith
  by_cases hr : 1 / 2 ≤ s.re
  · have hp7 : (|s.im| + 2) ^ 2 ≤ (|s.im| + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := zeta_right hZ hr hs2
      _ ≤ 300000 * (|s.im| + 2) ^ 7 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ |s.im| + 2) 2]
  · push_neg at hr
    by_cases hn : 1 / 2 ≤ ‖s‖
    · calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := zeta_left hZ hs1 hr hn
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr; norm_num
    · push_neg at hn
      have hK : ∀ z ∈ frontier (Metric.ball (0 : ℂ) (1 / 2)),
          ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by
        intro z hz
        rw [frontier_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere_zero_iff_norm] at hz
        have hre : |z.re| ≤ 1 / 2 := (Complex.abs_re_le_norm z).trans hz.le
        have him : |z.im| ≤ 1 / 2 := (Complex.abs_im_le_norm z).trans hz.le
        have hzi := abs_nonneg z.im
        rcases lt_or_ge z.re (1 / 2) with hlt | hge
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (|z.im| + 2) ^ 7 :=
                zeta_left hZ (by linarith [(abs_le.1 hre).1]) hlt (by rw [hz])
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by gcongr; linarith
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 51 * (|z.im| + 2) ^ 2 :=
                zeta_right hZ hge (by linarith [(abs_le.1 hre).2])
            _ ≤ 51 * (5 / 2 : ℝ) ^ 2 := by gcongr; linarith
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by norm_num
      have hd : DiffContOnCl ℂ (fun z => (z - 1) * riemannZeta z) (Metric.ball (0 : ℂ) (1 / 2)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        intro z hz
        have hz1 : z ≠ 1 := by
          intro h
          rw [h, Metric.mem_closedBall, dist_zero_right, norm_one] at hz
          norm_num at hz
        exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz1)).differentiableWithinAt
      have hmem : s ∈ closure (Metric.ball (0 : ℂ) (1 / 2)) := subset_closure (mem_ball_zero_iff.2 hn)
      have hb := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hK hmem
      calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := hb
        _ ≤ 300000 * 2 ^ 7 := by norm_num
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructB
section
noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

section prim
variable {N : ℕ}

lemma factorsThrough_inv {χ : DirichletCharacter ℂ N} {d : ℕ} (h : χ.FactorsThrough d) :
    (χ⁻¹).FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

lemma conductor_inv (χ : DirichletCharacter ℂ N) : (χ⁻¹).conductor = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  simp only [DirichletCharacter.conductorSet, Set.mem_setOf_eq]
  exact ⟨fun h => by simpa using factorsThrough_inv h, factorsThrough_inv⟩

lemma isPrimitive_inv {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  have h' : χ.conductor = N := h
  show (χ⁻¹).conductor = N
  rw [conductor_inv, h']

lemma level_eq_one_of_primitive_one [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive)
    (h1 : χ = 1) : N = 1 := by
  have h' : χ.conductor = N := h
  rw [h1, DirichletCharacter.conductor_one] at h'
  exact h'.symm

end prim

variable {N : ℕ} [NeZero N]

lemma completed_ne_zero_right (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 ≤ s.re)
    (h1 : χ ≠ 1 ∨ s ≠ 1) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  rw [h0, zero_div] at h2
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 hs h2

lemma completed_ne_zero_left {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) (h1 : χ ≠ 1 ∨ s ≠ 0) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hp := (isPrimitive_inv hχ).completedLFunction_one_sub s
  rw [inv_inv, h0, mul_zero] at hp
  refine completed_ne_zero_right χ⁻¹ (s := 1 - s) (by simp; linarith) ?_ hp
  rcases h1 with h | h
  · left
    exact fun h' => h (inv_eq_one.mp h')
  · right
    intro h'
    apply h
    linear_combination -h'

theorem zeroLocus : ZeroLocus := by
  intro N _ χ hχ s hs hs1 hL
  by_cases hre1 : 1 ≤ s.re
  · exact absurd hL (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hre1)
  by_cases hre0 : 0 < s.re
  · left
    exact ⟨hre0, by linarith⟩
  push_neg at hre1 hre0
  right
  by_cases hc : s = 0 ∧ χ = 1
  · exfalso
    obtain ⟨rfl, rfl⟩ := hc
    have hN := level_eq_one_of_primitive_one hχ rfl
    subst hN
    rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero] at hL
    norm_num at hL
  have hc' : χ ≠ 1 ∨ s ≠ 0 := by tauto
  have hne := completed_ne_zero_left hχ hre0 hc'
  have hsN : s ≠ 0 ∨ N ≠ 1 := by
    rcases hc' with h | h
    · right
      intro hN
      subst hN
      exact h (DirichletCharacter.level_one χ)
    · left
      exact h
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hsN
  rw [hL, eq_comm, div_eq_zero_iff] at hdiv
  rcases hdiv with h | hg
  · exact absurd h hne
  rcases DirichletCharacter.even_or_odd χ with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    simp at hn
    refine Or.inl ⟨hn, he, ?_⟩
    intro h1
    exact hc ⟨hn, h1⟩
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    refine Or.inr ⟨?_, ho⟩
    simp at hn
    linear_combination hn

private lemma exists_differentiable_Gammaℝ_inv_eq_mul : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
    ∀ z : ℂ, (Gammaℝ z)⁻¹ = z * g z := by
  refine ⟨fun s => (Real.pi : ℂ) ^ (s / 2) * (1 / 2 * (Complex.Gamma (s / 2 + 1))⁻¹), ?_, ?_, ?_⟩
  · refine Differentiable.mul ?_ ?_
    · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (differentiable_const _).mul
        (Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const (2 : ℂ)).add_const 1))
  · simp [Complex.Gamma_one]
  · intro z
    rw [Complex.Gammaℝ_def, neg_div, Complex.cpow_neg, mul_inv, inv_inv]
    by_cases hz : z = 0
    · subst hz
      simp [Complex.Gamma_zero]
    · have key : (Complex.Gamma (z / 2))⁻¹ = z * (1 / 2 * (Complex.Gamma (z / 2 + 1))⁻¹) := by
        rw [Complex.Gamma_add_one _ (div_ne_zero hz two_ne_zero), mul_inv]
        have h2 : z * (1 / 2) * (z / 2)⁻¹ = 1 := by field_simp
        calc (Complex.Gamma (z / 2))⁻¹
            = (z * (1 / 2) * (z / 2)⁻¹) * (Complex.Gamma (z / 2))⁻¹ := by rw [h2, one_mul]
          _ = _ := by ring
      rw [key]
      ring

theorem mult_zero_of_even {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (he : χ.Even)
    (h1 : χ ≠ 1) : LFunction χ 0 = 0 ∧ analyticOrderNatAt (LFunction χ) 0 = 1 := by
  obtain ⟨g, hgd, hg0, hgz⟩ := exists_differentiable_Gammaℝ_inv_eq_mul
  have hN1 : N ≠ 1 := by
    intro hN
    subst hN
    exact h1 (DirichletCharacter.level_one χ)
  have hLeq : ∀ s, LFunction χ s = completedLFunction χ s * (s * g s) := by
    intro s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1),
      he.gammaFactor_def, div_eq_mul_inv, hgz]
  have hc0 : completedLFunction χ 0 ≠ 0 := completed_ne_zero_left hχ (by simp) (Or.inl h1)
  have hcd : Differentiable ℂ (completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction h1
  refine ⟨by rw [hLeq]; simp, ?_⟩
  have hLa : AnalyticAt ℂ (LFunction χ) 0 := (DirichletCharacter.differentiable_LFunction h1).analyticAt 0
  have hord : analyticOrderAt (LFunction χ) 0 = ((1 : ℕ) : ℕ∞) := by
    rw [hLa.analyticOrderAt_eq_natCast]
    refine ⟨fun s => completedLFunction χ s * g s, (hcd.mul hgd).analyticAt 0, mul_ne_zero hc0 hg0, ?_⟩
    filter_upwards with z
    rw [hLeq]
    simp only [sub_zero, pow_one, smul_eq_mul]
    ring
  simp [analyticOrderNatAt, hord]

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectProofs
section
namespace PI.EF

open Complex

theorem rectResidue : RectResidue := by
  intro x₀ x₁ y₀ y₁ H Z wt e u hu h1 h2 h3 h4 hH hZ
  exact Rect.rect_residue (z := ⟨x₀, y₀⟩) (w := ⟨x₁, y₁⟩) Z wt e hu
    ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩ hH
    (fun ρ hρ => ⟨(hZ ρ hρ).1, (hZ ρ hρ).2⟩)

end PI.EF
end

