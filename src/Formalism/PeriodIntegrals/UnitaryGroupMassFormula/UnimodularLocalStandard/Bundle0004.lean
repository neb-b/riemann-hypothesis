module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.IsKTheta
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section IsKsec
variable (b : ℤ) (d : ℕ)

def IsK (t : ℂ) : Prop := ∃ p q r : ℤ, r ≠ 0 ∧ (r : ℂ) * t = p + q * cmTheta b d

variable {b d}

lemma isK_int (n : ℤ) : IsK b d n := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨n, 0, 1, one_ne_zero, by simp⟩

lemma isK_theta : IsK b d (cmTheta b d) := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨0, 1, 1, one_ne_zero, by simp⟩

lemma isK_add {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t + t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨r' * p + r * p', r' * q + r * q', r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination (r' : ℂ) * h + (r : ℂ) * h'

lemma isK_neg {t : ℂ} (h : IsK b d t) : IsK b d (-t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨-p, -q, r, hr, ?_⟩
  push_cast
  linear_combination -h

lemma isK_sub {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t - t') := by
  rw [sub_eq_add_neg]
  exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add h (PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg h')

private lemma conj_cmTheta : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
  unfold cmTheta
  simp only [map_div₀, map_add (f := _), map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

lemma isK_conj {t : ℂ} (h : IsK b d t) : IsK b d (conj t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  have h2 : (r : ℂ) * conj t = p + q * conj (cmTheta b d) := by
    have h3 := congrArg conj h
    simpa using h3
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p + q * b, -q, r, hr, ?_⟩
  rw [h2, PI.UnitaryGroupMassFormula.UnimodLocStd.conj_cmTheta]
  push_cast
  ring

variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn

lemma isK_mul {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t * t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p * p' - q * q' * e, p * q' + q * p' + q * q' * b, r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination ((r' : ℂ) * t') * h + ((p : ℂ) + q * cmTheta b d) * h' - ((q : ℂ) * q') * hn

lemma isK_inv {t : ℂ} (h : IsK b d t) : IsK b d t⁻¹ := by
  by_cases ht : t = 0
  · rw [ht, inv_zero]
    simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  obtain ⟨p, q, r, hr, h⟩ := h
  have hrt : (r : ℂ) * t ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hr) ht

  have hz : ((p ^ 2 + p * q * b + q ^ 2 * e : ℤ) : ℂ) =
      (r : ℂ) * t * (p + q * b - q * cmTheta b d) := by
    rw [h]
    push_cast
    linear_combination (-(q : ℂ) ^ 2) * hn
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  by_cases hN : p ^ 2 + p * q * b + q ^ 2 * e = 0
  ·
    have hw : (p : ℂ) + q * b - q * cmTheta b d = 0 := by
      have h0 : (r : ℂ) * t * (p + q * b - q * cmTheta b d) = 0 := by
        rw [← hz, hN, Int.cast_zero]
      exact (mul_eq_zero.mp h0).resolve_left hrt
    have hk : (r : ℂ) * t = ((2 * p + q * b : ℤ) : ℂ) := by
      rw [h]
      push_cast
      linear_combination -hw
    have hk0 : (2 * p + q * b : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hk
      exact hrt hk
    refine ⟨r, 0, 2 * p + q * b, hk0, ?_⟩
    rw [← hk, mul_inv_cancel_right₀ ht]
    simp
  · refine ⟨r * (p + q * b), -(r * q), p ^ 2 + p * q * b + q ^ 2 * e, hN, ?_⟩
    rw [hz]
    field_simp
    push_cast
    ring

lemma isK_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsK b d (f i)) : IsK b d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end IsKsec

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepArith
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Arith

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

theorem rep_sqrt_sq : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d), Complex.ofReal_natCast]

theorem rep_conj_theta : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  simp only [cmTheta, map_div₀, map_add (f := _), map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat]
  ring

theorem rep_theta_add_conj : cmTheta b d + conj (cmTheta b d) = b := by
  rw [rep_conj_theta b d, cmTheta]
  ring

theorem rep_theta_mul_conj (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d * conj (cmTheta b d) = (a : ℂ) * c := by
  have h4 : ((4 * (a : ℤ) * c : ℤ) : ℂ) = ((b ^ 2 + d : ℤ) : ℂ) := by rw [hOK]
  push_cast at h4
  have hs := rep_sqrt_sq d
  rw [rep_conj_theta b d, cmTheta]
  linear_combination (-1 / 4 : ℂ) * h4 - (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq +
    (1 / 4 : ℂ) * hs

theorem rep_elt_norm (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (p q : ℤ) :
    (lam * ((p : ℂ) * a + q * cmTheta b d)) * conj (lam * ((p : ℂ) * a + q * cmTheta b d)) =
      (Complex.normSq lam : ℂ) * a * ((a * p ^ 2 + b * p * q + c * q ^ 2 : ℤ) : ℂ) := by
  have h1 := rep_theta_add_conj b d
  have h2 := rep_theta_mul_conj a b c d hOK
  have hN := Complex.mul_conj lam
  simp only [map_mul, map_add (f := _), map_intCast, map_natCast]
  push_cast
  linear_combination ((p : ℂ) * a + q * cmTheta b d) * ((p : ℂ) * a + q * conj (cmTheta b d)) * hN +
    (Complex.normSq lam : ℂ) * p * q * a * h1 + (Complex.normSq lam : ℂ) * q ^ 2 * h2

theorem rep_omega1 : (cmL a b d ha hd lam hlam).ω₁ = lam * a := rfl
theorem rep_omega2 : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := rfl

theorem rep_area_ne : area (cmL a b d ha hd lam hlam) ≠ 0 := by
  rw [area, rep_omega1, rep_omega2, abs_ne_zero]
  have him : (conj (lam * a) * (lam * cmTheta b d)).im =
      Complex.normSq lam * a * (Real.sqrt d / 2) := by
    rw [show conj (lam * a) * (lam * cmTheta b d) = (lam * conj lam) * a * cmTheta b d by
      simp only [map_mul, map_natCast]; ring, Complex.mul_conj,
      show ((Complex.normSq lam : ℝ) : ℂ) * a * cmTheta b d =
        ((Complex.normSq lam * a : ℝ) : ℂ) * cmTheta b d by push_cast; ring, Complex.im_ofReal_mul]
    simp [cmTheta]
  rw [him]
  exact ne_of_gt (mul_pos (mul_pos (Complex.normSq_pos.2 hlam) (Nat.cast_pos.2 ha))
    (div_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hd)) two_pos))

def repKappa : ℂ := ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * (Complex.normSq lam : ℂ) * a

theorem rep_kappa_ne : repKappa a b d ha hd lam hlam ≠ 0 := by
  unfold repKappa
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.2 (rep_area_ne a b d ha hd lam hlam)))
    (Complex.ofReal_ne_zero.2 (Complex.normSq_pos.2 hlam).ne')) (Nat.cast_ne_zero.2 ha.ne')

variable (m : Type) [Fintype m] [DecidableEq m]

theorem rep_norm_f (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (x y : ℤ) (i₀ : m) :
    stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
      repKappa a b d ha hd lam hlam * ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) := by
  rw [rep_H_apply, Fintype.sum_eq_single i₀ (fun i hi => by simp [fvec, hi])]
  simp only [fvec, Pi.single_eq_same]
  rw [rep_elt_norm a b c d lam hOK x y]
  unfold repKappa
  ring

theorem rep_fvec_mem (x y : ℤ) (i₀ : m) : fvec a b d lam x y i₀ ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup]
  intro i
  by_cases h : i = i₀
  · subst h
    simp only [fvec, Pi.single_eq_same]
    exact PeriodPair.mem_lattice.2 ⟨x, y, by rw [rep_omega1, rep_omega2]; ring⟩
  · simp only [fvec, Pi.single_eq_of_ne h]
    exact zero_mem _

end Arith

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

