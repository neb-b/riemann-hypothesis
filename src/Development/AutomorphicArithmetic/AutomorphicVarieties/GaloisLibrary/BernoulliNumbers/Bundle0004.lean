module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denchar
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_denchar :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (Φ : ZMod N → R) (A : Subring R), 0 < N → (∀ a, Φ a ∈ A) → (den N k : R) * genB k Φ ∈ A := by
  intro R _ _ N k Φ A hN hΦ
  unfold genB
  rw [Finset.mul_sum]
  refine A.sum_mem fun a _ => ?_
  obtain ⟨z, hz⟩ := b_denint N k a hN
  have h : (den N k : R) * algebraMap ℚ R (bcoef N k a) = (z : R) := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, hz, map_intCast]
  rw [mul_left_comm, h]
  exact A.mul_mem (hΦ _) (intCast_mem A z)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denupper
section
open Finset UpperTheory.V.Bern

private theorem bernoulli_denominator_bound {N M : ℕ} (k : ℕ) (Φ : ZMod M → ℂ) (hM : 0 < M) (hMN : M ≤ N)
    (hΦ : ∀ a, ‖Φ a‖ ≤ 1) : ‖(den N k : ℂ) * genB k Φ‖ ≤ bnd N k := by
  have hb := b_upper k Φ hM hΦ
  have hp : (primorial (k + 1) : ℝ) ≤ 4 ^ (k + 1) := by exact_mod_cast primorial_le_four_pow (k + 1)
  have h4 : (4 : ℝ) ^ k ≤ (2 * Real.pi) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
  have hpi : 0 < (2 * Real.pi) ^ k := by positivity
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  rw [norm_mul, Complex.norm_natCast, den, bnd]
  push_cast
  calc (N : ℝ) * (primorial (k + 1) : ℝ) * ‖genB k Φ‖
      ≤ N * 4 ^ (k + 1) * (4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k) := by
        gcongr
        exact hb.trans (by gcongr)
    _ = 16 * (N : ℝ) ^ (k + 1) * k.factorial * (4 ^ k / (2 * Real.pi) ^ k) := by ring
    _ ≤ 16 * (N : ℝ) ^ (k + 1) * k.factorial * 1 := by
        gcongr
        rw [div_le_one hpi]
        exact h4
    _ = _ := mul_one _

theorem UpperTheory.V.Bern.b_denupper :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter ℂ N), ‖(den N k : ℂ) * genB k χ‖ ≤ bnd N k ∧ ‖(den N k : ℂ) * Bprim k χ‖ ≤ bnd N k ∧ 1 ≤ bnd N k := by
  intro N _ k χ
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨bernoulli_denominator_bound k _ hN le_rfl (fun a => χ.norm_le_one a), ?_, ?_⟩
  · exact bernoulli_denominator_bound k _ (Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (Nat.le_of_dvd hN χ.conductor_dvd_level) (fun a => χ.primitiveCharacter.norm_le_one a)
  · have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (k + 1) := one_le_pow₀ (by exact_mod_cast hN)
    have h2 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
    unfold bnd
    nlinarith [mul_le_mul h1 h2 zero_le_one (zero_le_one.trans h1)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Hurzero
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_hurzero :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ) := by
  intro x hx0 hx1
  set U : Set ℂ := {s | -1 / 2 < s.re} ∩ Metric.ball 0 3 with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U := ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hG : DifferentiableOn ℂ (fun s => HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s
      - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ))) U := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.sub_const
    rcases eq_or_ne s 1 with rfl | hs
    · have := (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div (x : UnitAddCircle)).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div ((1 : ℝ) : UnitAddCircle))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp only [Pi.sub_apply]; ring)
    · exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta _ hs)
  have hev : ∀ᶠ s in nhds (2 : ℂ), 1 < s.re :=
    (Complex.continuous_re.tendsto 2).eventually (lt_mem_nhds (by norm_num))
  have h2 : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by simp; norm_num⟩
  have heq := ((b_termdiff x hx0 hx1).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) hUc h2 (hev.mono fun s hs => b_termsum x hx0 hx1 s hs)
  have h0 := heq (show (0 : ℂ) ∈ U from ⟨by simp; norm_num, by simp⟩)
  have h1 : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2 := by
    rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero, riemannZeta_zero]
  simp only [neg_zero, Complex.cpow_zero, sub_self, mul_zero, tsum_zero] at h0
  rw [h1] at h0
  linear_combination -h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.SumIccMulEq
section
open Finset UpperTheory.V.Bern

private theorem sum_Icc_one_eq {R : Type} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∑ x ∈ Icc 1 n, f x = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private theorem sum_Icc_mul_eq {R : Type} [AddCommMonoid R] (f : ℕ → R) (N m : ℕ) :
    ∑ x ∈ Icc 1 (N * m), f x = ∑ j ∈ range m, ∑ a ∈ Icc 1 N, f (a + j * N) := by
  simp_rw [sum_Icc_one_eq]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

theorem UpperTheory.V.Bern.b_comp :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N M : ℕ} (h : N ∣ M) (k : ℕ) (Φ : ZMod N → R), 0 < M → genB k (fun a : ZMod M => Φ (ZMod.castHom h (ZMod N) a)) = genB k Φ := by
  intro R _ _ N M h k Φ hM
  obtain ⟨m, rfl⟩ := h
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  unfold genB
  rw [sum_Icc_mul_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [b_raabe N m k _ hN hm, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [map_natCast]
  simp
end

