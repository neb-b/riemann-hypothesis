module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.IntOnOfBdd
section
open MeasureTheory Set UpperHalfPlane

private lemma half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private lemma intOn_of_bdd (hF : UpperTheory.V.Af.Rs.FdFin) (φ : ℍ → ℝ) (hc : Continuous φ) (B : ℝ)
    (hB : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ B) : IntegrableOn φ ModularGroup.fd :=
  Measure.integrableOn_of_bounded hF.2.ne hc.aestronglyMeasurable
    ((ae_restrict_iff' hF.1).2 (Filter.Eventually.of_forall hB))

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.tTop :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdPos → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZLow → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TTop := by
  intro hfd hpos hw hzd hzl hzi L _ G hG hre hex M
  obtain ⟨hGc, C', hC'⟩ := hG
  obtain ⟨C, hC⟩ := hzd L
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (Fintype.card (Fin 2 → ZMod L) : ℝ) := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hNpos : 0 < N := by linarith
  have hcard : ∀ x : ℝ, (Finset.univ : Finset (Fin 2 → ZMod L)).card • x = N * x := by
    intro x
    rw [Finset.card_univ, nsmul_eq_mul, hN]
  obtain ⟨φ, hφ⟩ : ∃ φ : ℍ → ℝ,
      φ = fun z => (∑ v, (G v z).re) / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℍ → ℝ, ψ = fun z => ∑ v, (G v z).re * z.im ^ 3 := ⟨_, rfl⟩
  have hreC : ∀ v, Continuous fun z => (G v z).re := fun v => Complex.continuous_re.comp (hGc v)
  have himC : Continuous fun z : ℍ => z.im := UpperHalfPlane.continuous_im
  have hnC : Continuous fun z : ℍ => ‖(z : ℂ)‖ := continuous_norm.comp UpperHalfPlane.continuous_coe
  have hden : ∀ z : ℍ, 0 < 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := fun z => by positivity
  have hφC : Continuous φ := by
    rw [hφ]
    exact (continuous_finsetSum _ (fun v _ => hreC v)).div
      (continuous_const.mul ((hnC.add continuous_const).pow 4)) (fun z => (hden z).ne')
  have hψC : Continuous ψ := by
    rw [hψ]
    exact continuous_finsetSum _ (fun v _ => (hreC v).mul (himC.pow 3))
  have hGb : ∀ v, ∀ z ∈ ModularGroup.fd,
      0 ≤ (G v z).re * z.im ^ 3 ∧ (G v z).re * z.im ^ 3 ≤ C' := by
    intro v z hz
    have hp : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    refine ⟨mul_nonneg (hre v z) hp, ?_⟩
    exact (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hp).trans (hC' v z (half_le_im hz))
  have hψb : ∀ z ∈ ModularGroup.fd, ‖ψ z‖ ≤ N * C' := by
    intro z hz
    rw [hψ, Real.norm_of_nonneg (Finset.sum_nonneg (fun v _ => (hGb v z hz).1))]
    exact (Finset.sum_le_card_nsmul _ _ _ (fun v _ => (hGb v z hz).2)).trans_eq (hcard _)
  have hφb : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ N * (8 * C') := by
    intro z hz
    have hs0 : 0 ≤ ∑ v, (G v z).re := Finset.sum_nonneg (fun v _ => hre v z)
    have h1 : 1 ≤ 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := by
      have : 1 ≤ (‖(z : ℂ)‖ + 1) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg (z : ℂ)])
      nlinarith
    rw [hφ, Real.norm_of_nonneg (div_nonneg hs0 (hden z).le)]
    refine (div_le_self hs0 h1).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ (fun v _ => ?_)).trans_eq (hcard _)
    have h8 := (hGb v z hz).2
    have h3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) (half_le_im hz) 3) (hre v z)
    norm_num at h3
    linarith
  have hφI := intOn_of_bdd hfd φ hφC _ hφb
  have hψI := intOn_of_bdd hfd ψ hψC _ hψb
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    rw [hφ]
    exact div_nonneg (Finset.sum_nonneg (fun v _ => hre v z)) (hden z).le
  obtain ⟨v0, z0, hz0, hv0⟩ := hex
  have hc : 0 < ∫ z in ModularGroup.fd, φ z := by
    refine hpos φ hφC hφ0 hφI z0 hz0 ?_
    rw [hφ]
    refine div_pos ?_ (hden z0)
    exact lt_of_lt_of_le hv0
      (Finset.single_le_sum (f := fun v => (G v z0).re) (fun v _ => hre v z0) (Finset.mem_univ v0))
  obtain ⟨c, hcd⟩ : ∃ c, c = ∫ z in ModularGroup.fd, φ z := ⟨_, rfl⟩
  rw [← hcd] at hc
  have hψint : ∫ z in ModularGroup.fd, ψ z ≤ N * C' * volume.real ModularGroup.fd :=
    (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hfd.2 hψb)
  obtain ⟨s, hs, hWs⟩ := hw.2 ((M + |C| * (N * C' * volume.real ModularGroup.fd)) / c)
  refine ⟨s, hs, ?_⟩
  have hpt : ∀ z ∈ ModularGroup.fd,
      Wsum s * φ z - |C| * ψ z ≤ (∑ v, G v z * (Zc L v s z : ℂ)).re := by
    intro z hz
    have hlow := hzl L s hs z hz
    have hp3 : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    have hZ : ∀ v, Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3 ≤ Zc L v s z := by
      intro v
      have hsum : ∑ v', Zc L v' s z ≤ N * (Zc L v s z + |C| * z.im ^ 3) := by
        refine (Finset.sum_le_card_nsmul _ _ _ (fun v' _ => ?_)).trans_eq (hcard _)
        have h1 := hC v v' s hs z hz
        have h2 := mul_le_mul_of_nonneg_right (le_abs_self C) hp3
        have h3 := neg_abs_le (Zc L v s z - Zc L v' s z)
        linarith
      have hq : 1 / 2 / (‖(z : ℂ)‖ + 1) ^ 4 * Wsum s =
          N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) := by
        have := hden z
        field_simp
      have h4 : N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) ≤ N * (Zc L v s z + |C| * z.im ^ 3) :=
        hq ▸ hlow.trans hsum
      have h5 := le_of_mul_le_mul_left h4 hNpos
      linarith
    rw [Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hφ, hψ]
    simp only
    rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have h6 := mul_le_mul_of_nonneg_left (hZ v) (hre v z)
    calc Wsum s * ((G v z).re / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) - |C| * ((G v z).re * z.im ^ 3)
        = (G v z).re * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3) := by ring
      _ ≤ (G v z).re * Zc L v s z := h6
  have hfI : IntegrableOn (fun z => ∑ v, G v z * (Zc L v s z : ℂ)) ModularGroup.fd :=
    integrable_finsetSum _ (fun v _ => hzi L G ⟨hGc, C', hC'⟩ s hs v v)
  have hre_eq : (∫ z in ModularGroup.fd, ∑ v, G v z * (Zc L v s z : ℂ)).re =
      ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re := (integral_re hfI).symm
  unfold TT
  rw [hre_eq]
  calc M ≤ Wsum s * c - |C| * (N * C' * volume.real ModularGroup.fd) := by
        have := (div_le_iff₀ hc).1 hWs
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (Wsum s * φ z - |C| * ψ z) := by
        rw [integral_sub (hφI.const_mul _) (hψI.const_mul _), integral_const_mul,
          integral_const_mul, ← hcd]
        have := mul_le_mul_of_nonneg_left hψint (abs_nonneg C)
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re :=
        setIntegral_mono_on ((hφI.const_mul _).sub (hψI.const_mul _)) hfI.re hfd.1 hpt
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.KerDiff
section
open UpperHalfPlane Set

namespace UpperTheory.V.Af.Rs

private lemma kd_pow {a b t m : ℝ} (hm : 1 ≤ m) (hb : m / 2 ≤ b) (hab : b ≤ a) (ht : 2 ≤ t) (ht' : t ≤ 4) :
    |a ^ (-t) - b ^ (-t)| ≤ 128 * (a - b) * m ^ (-3 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  set A := a ^ t with hA
  set B := b ^ t with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos ha0 t
  have hBpos : 0 < B := Real.rpow_pos_of_pos hb0 t
  have hneg_a : a ^ (-t) = A⁻¹ := Real.rpow_neg ha0.le t
  have hneg_b : b ^ (-t) = B⁻¹ := Real.rpow_neg hb0.le t
  have hBA : B ≤ A := Real.rpow_le_rpow hb0.le hab (by linarith)
  have hbern : 1 + t * (b / a - 1) ≤ B / A := by
    have h := one_add_mul_self_le_rpow_one_add (s := b / a - 1)
      (by have := div_nonneg hb0.le ha0.le; linarith) (p := t) (by linarith)
    rw [show 1 + (b / a - 1) = b / a by ring, Real.div_rpow hb0.le ha0.le] at h
    exact h
  have hsub : |a ^ (-t) - b ^ (-t)| = B⁻¹ - A⁻¹ := by
    rw [hneg_a, hneg_b, abs_sub_comm, abs_of_nonneg]
    rw [sub_nonneg]
    exact inv_anti₀ hBpos hBA
  have hkey : B⁻¹ - A⁻¹ ≤ t * (a - b) / b / B := by
    have h1 : B⁻¹ - A⁻¹ = (1 - B / A) / B := by field_simp
    have h2 : 1 - B / A ≤ t * (a - b) / b := by
      have h3 : t * (1 - b / a) ≤ t * (a - b) / b := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [one_sub_div ha0.ne']
        exact div_le_div_of_nonneg_left (by linarith) hb0 hab
      nlinarith
    rw [h1]
    exact div_le_div_of_nonneg_right h2 hBpos.le
  have hbB : m ^ 3 / 32 ≤ b * B := by
    have e1 : (m / 2) ^ (t + 1) ≤ b ^ (t + 1) := Real.rpow_le_rpow (by positivity) hb (by linarith)
    have e2 : b ^ (t + 1) = b * B := by rw [Real.rpow_add_one hb0.ne']; ring
    have e3 : (m / 2) ^ (t + 1) = m ^ (t + 1) / 2 ^ (t + 1) := Real.div_rpow hm0.le (by norm_num) _
    have e4 : m ^ (3 : ℝ) ≤ m ^ (t + 1) := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
    have e5 : (2 : ℝ) ^ (t + 1) ≤ 2 ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have e6 : (2 : ℝ) ^ (5 : ℝ) = 32 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have e7 : m ^ (3 : ℝ) = m ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2pos : 0 < (2 : ℝ) ^ (t + 1) := by positivity
    have h8 : m ^ 3 / 32 ≤ m ^ (t + 1) / 2 ^ (t + 1) := by
      rw [div_le_div_iff₀ (by norm_num) h2pos]
      have hm3 : 0 ≤ m ^ 3 := by positivity
      rw [← e7] at hm3 ⊢
      rw [e6] at e5
      nlinarith
    linarith
  have hm3pos : 0 < m ^ 3 := by positivity
  have hmneg : m ^ (-3 : ℝ) = (m ^ 3)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hsub, hmneg]
  refine hkey.trans ?_
  rw [div_div]
  have hbBpos : 0 < b * B := by positivity
  rw [div_le_iff₀ hbBpos]
  have hab' : 0 ≤ a - b := by linarith
  have : t * (a - b) ≤ 4 * (a - b) := by nlinarith
  have h32 : 128 * (a - b) * (m ^ 3)⁻¹ * (m ^ 3 / 32) = 4 * (a - b) := by
    field_simp
    ring
  have hc : 0 ≤ 128 * (a - b) * (m ^ 3)⁻¹ := by positivity
  calc t * (a - b) ≤ 4 * (a - b) := this
    _ = 128 * (a - b) * (m ^ 3)⁻¹ * (m ^ 3 / 32) := h32.symm
    _ ≤ 128 * (a - b) * (m ^ 3)⁻¹ * (b * B) := mul_le_mul_of_nonneg_left hbB hc

private lemma kd_abs (x : Fin 2 → ℤ) (i : Fin 2) : |(x i : ℝ)| ≤ ‖x‖ := by
  have := norm_le_pi_norm x i
  rwa [Int.norm_eq_abs] at this

private lemma kd_one {x : Fin 2 → ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (kd_abs x i)

private lemma kd_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    1 ≤ z.re ^ 2 + z.im ^ 2 ∧ -(1 / 2) ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 1 / 2 ≤ z.im := by
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy := z.im_pos
  obtain ⟨h1, h2⟩ := hz
  rw [Complex.normSq_apply] at h1
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1 h2
  rw [abs_le] at h2
  refine ⟨by nlinarith, h2.1, h2.2, by nlinarith⟩

private lemma kd_low (x : Fin 2 → ℤ) {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    ‖x‖ / 2 ≤ ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := kd_fd hz
  set c : ℝ := (x 0 : ℝ)
  set d : ℝ := (x 1 : ℝ)
  have hsq : ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ 2 = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [c, d]
    ring
  have hmax : ‖x‖ ≤ max |c| |d| := by
    rw [pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))]
    intro i
    rw [Int.norm_eq_abs]
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hN : ‖x‖ ^ 2 ≤ c ^ 2 + d ^ 2 := by
    have hN0 := norm_nonneg x
    rcases le_max_iff.mp hmax with h | h
    · have : ‖x‖ ^ 2 ≤ |c| ^ 2 := pow_le_pow_left₀ hN0 h 2
      rw [sq_abs] at this
      nlinarith
    · have : ‖x‖ ^ 2 ≤ |d| ^ 2 := pow_le_pow_left₀ hN0 h 2
      rw [sq_abs] at this
      nlinarith
  have hcd : |2 * c * d * z.re| ≤ |c * d| := by
    rw [show 2 * c * d * z.re = (c * d) * (2 * z.re) by ring, abs_mul]
    have : |2 * z.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc |c * d| * |2 * z.re| ≤ |c * d| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |c * d| := mul_one _
  have hcd2 : 2 * |c * d| ≤ c ^ 2 + d ^ 2 := by
    rw [abs_mul]
    have := sq_nonneg (|c| - |d|)
    nlinarith [sq_abs c, sq_abs d]
  have hlow : (‖x‖ / 2) ^ 2 ≤ ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ 2 := by
    rw [hsq]
    have e : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 = c ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * c * d * z.re + d ^ 2 := by ring
    rw [e]
    have := neg_abs_le (2 * c * d * z.re)
    have hc2 : c ^ 2 ≤ c ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
      nlinarith [sq_nonneg c]
    nlinarith
  have hw0 := norm_nonneg ((x 0 : ℂ) * z + (x 1 : ℂ))
  nlinarith [norm_nonneg x]

private lemma kd_up (x : Fin 2 → ℤ) {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ≤ 4 * ‖x‖ * z.im := by
  obtain ⟨h1, h2, h3, h4⟩ := kd_fd hz
  have hz' : ‖(z : ℂ)‖ ≤ 1 / 2 + z.im := by
    have := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    rw [abs_of_pos z.im_pos] at this
    have : |z.re| ≤ 1 / 2 := abs_le.mpr ⟨h2, h3⟩
    linarith
  have hN0 := norm_nonneg x
  calc ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ≤ ‖(x 0 : ℂ)‖ * ‖(z : ℂ)‖ + ‖(x 1 : ℂ)‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ ‖x‖ * (1 / 2 + z.im) + ‖x‖ := by
        rw [Complex.norm_intCast, Complex.norm_intCast]
        have a0 := kd_abs x 0
        have a1 := kd_abs x 1
        have := norm_nonneg (z : ℂ)
        nlinarith [abs_nonneg ((x 0 : ℤ) : ℝ)]
    _ ≤ 4 * ‖x‖ * z.im := by nlinarith

private lemma kd_ker (s : ℝ) (x : Fin 2 → ℤ) (z : ℍ) :
    ker s x z = z.im ^ s * ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ (-(2 * s)) := by
  unfold ker
  have hy := z.im_pos
  rw [Complex.normSq_eq_norm_sq, Real.div_rpow hy.le (by positivity),
    Real.rpow_neg (norm_nonneg _), Real.rpow_mul (norm_nonneg _), div_eq_mul_inv]
  norm_num

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.kerDiff :
    UpperTheory.V.Af.Rs.KerDiff := by
  refine ⟨1024, by norm_num, ?_⟩
  intro s hs x x' hx hx' z hz
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨-, -, -, hy2⟩ := kd_fd hz
  have hy : 0 < z.im := z.im_pos
  rw [kd_ker, kd_ker]
  set w : ℂ := (x 0 : ℂ) * z + (x 1 : ℂ) with hw
  set w' : ℂ := (x' 0 : ℂ) * z + (x' 1 : ℂ) with hw'
  set S : ℝ := ‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ) with hS
  have hS1 : 0 ≤ ‖x‖ ^ (-3 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hS2 : 0 ≤ ‖x'‖ ^ (-3 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hS0 : 0 ≤ S := by positivity
  have hdiff : ‖w‖ - ‖w'‖ ≤ 4 * ‖x - x'‖ * z.im ∧ ‖w'‖ - ‖w‖ ≤ 4 * ‖x - x'‖ * z.im := by
    have e : w - w' = (((x - x') 0 : ℤ) : ℂ) * z + (((x - x') 1 : ℤ) : ℂ) := by
      simp only [hw, hw', Pi.sub_apply, Int.cast_sub]
      ring
    have hu := kd_up (x - x') hz
    rw [← e] at hu
    have h1 := abs_norm_sub_norm_le w w'
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hD : |‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s))| ≤ 128 * (4 * ‖x - x'‖ * z.im) * S := by
    rcases le_total ‖w'‖ ‖w‖ with h | h
    · have := kd_pow (kd_one hx') (kd_low x' hz) h (by linarith : (2 : ℝ) ≤ 2 * s) (by linarith)
      calc _ ≤ 128 * (‖w‖ - ‖w'‖) * ‖x'‖ ^ (-3 : ℝ) := this
        _ ≤ 128 * (4 * ‖x - x'‖ * z.im) * ‖x'‖ ^ (-3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hS2
            linarith [hdiff.1]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have := norm_nonneg (x - x')
            positivity
    · rw [abs_sub_comm]
      have := kd_pow (kd_one hx) (kd_low x hz) h (by linarith : (2 : ℝ) ≤ 2 * s) (by linarith)
      calc _ ≤ 128 * (‖w'‖ - ‖w‖) * ‖x‖ ^ (-3 : ℝ) := this
        _ ≤ 128 * (4 * ‖x - x'‖ * z.im) * ‖x‖ ^ (-3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hS1
            linarith [hdiff.2]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have := norm_nonneg (x - x')
            positivity
  have hys : z.im ^ s ≤ 2 * z.im ^ 2 := by
    rcases le_total z.im 1 with h | h
    · have h1 : z.im ^ s ≤ z.im ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy h hs1
      rw [Real.rpow_one] at h1
      nlinarith
    · have h1 : z.im ^ s ≤ z.im ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs2
      rw [Real.rpow_two] at h1
      nlinarith
  have hyspos : 0 ≤ z.im ^ s := Real.rpow_nonneg hy.le _
  rw [← mul_sub, abs_mul, abs_of_nonneg hyspos]
  calc z.im ^ s * |‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s))|
      ≤ (2 * z.im ^ 2) * (128 * (4 * ‖x - x'‖ * z.im) * S) :=
        mul_le_mul hys hD (abs_nonneg _) (by positivity)
    _ = 1024 * ‖x - x'‖ * z.im ^ 3 * S := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.LBd
section
theorem UpperTheory.V.Af.Rs.lBd :
    UpperTheory.V.Af.Rs.LBd := by
  intro L _ ψ s hs
  set f : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hf
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hg
  have hs2 : (2 * s) ≠ 0 := by linarith
  have hbd : ∀ n, ‖f n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf, hg, Real.zero_rpow hs2]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ (2 * s) := Real.rpow_pos_of_pos (by linarith) _
      have hle : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (2 * s) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      rw [Real.rpow_two] at hle
      simp only [hf, hg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      calc ‖ψ n‖ / (n : ℝ) ^ (2 * s) ≤ 1 / (n : ℝ) ^ (2 * s) :=
            div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) hpos.le
        _ ≤ 1 / (n : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hle
  have hgs : HasSum g (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hsum : Summable f := Summable.of_norm_bounded hgs.summable hbd
  refine ⟨hsum, ?_⟩
  have hg2 : HasSum (fun n => g (n + 2)) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := g) 2).mpr hgs
    simpa [Finset.sum_range_succ, hg] using this
  have htail : ‖∑' n, f (n + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 :=
    tsum_of_norm_bounded hg2 (fun n => hbd (n + 2))
  have hsplit : UpperTheory.V.Af.Rs.Lps ψ s = 1 + ∑' n, f (n + 2) := by
    rw [UpperTheory.V.Af.Rs.Lps, ← hsum.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ, hf, Real.zero_rpow hs2]
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h1 := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  rw [hsplit]
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 2)))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  · have := norm_add_le (1 : ℂ) (∑' n, f (n + 2))
    rw [norm_one] at this
    linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.MelSum
section
noncomputable section

open MeasureTheory Set

namespace UpperTheory.V.Af.Rs

private lemma melSum_int {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    IntegrableOn (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := t - 1) (p := 1) (b := r) (by linarith) one_pos hr).const_mul a
  refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring

private lemma melSum_val {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    ∫ y in Ioi (0 : ℝ), a * Real.exp (-r * y) * y ^ (t - 1) = a * ((1 / r) ^ t * Real.Gamma t) := by
  have e : (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) =
      fun y => a * (y ^ (t - 1) * Real.exp (-(r * y))) := by
    funext y
    rw [neg_mul]
    ring
  rw [e, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ht hr]

theorem melSum : MelSum := by
  intro c P t ht hc hP hI
  have hΓ : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
  have h4 : 0 < 4 * Real.pi := by positivity
  have hCpos : 0 < (4 * Real.pi) ^ t / Real.Gamma t := div_pos (Real.rpow_pos_of_pos h4 t) hΓ
  have hr : ∀ n : ℕ, 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hval : ∀ n : ℕ, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t =
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ),
        c (n + 1) * Real.exp (-(4 * Real.pi * ((n + 1 : ℕ) : ℝ)) * y) * y ^ (t - 1) := by
    intro n
    rw [melSum_val ht (hr n)]
    have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Real.div_rpow zero_le_one (hr n).le, Real.one_rpow, Real.mul_rpow h4.le hm.le]
    have h5 : 0 < ((n + 1 : ℕ) : ℝ) ^ t := Real.rpow_pos_of_pos hm t
    have h6 : 0 < (4 * Real.pi) ^ t := Real.rpow_pos_of_pos h4 t
    field_simp
  have hbound : ∀ N, ∑ n ∈ Finset.range N, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t ≤
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ), P y * y ^ (t - 1) := by
    intro N
    simp_rw [hval]
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun n _ => melSum_int ht (hr n) _)]
    apply mul_le_mul_of_nonneg_left _ hCpos.le
    apply setIntegral_mono_on
    · exact integrable_finsetSum _ (fun n _ => melSum_int ht (hr n) _)
    · exact hI
    · exact measurableSet_Ioi
    · intro y hy
      have hy' : 0 < y := hy
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy'.le _)
      have h1 : ∑ n ∈ Finset.range (N + 1), c n * Real.exp (-(4 * Real.pi * n) * y) ≤ P y :=
        sum_le_hasSum _ (fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le) (hP y hy')
      rw [Finset.sum_range_succ'] at h1
      have h0 : 0 ≤ c 0 * Real.exp (-(4 * Real.pi * ((0 : ℕ) : ℝ)) * y) :=
        mul_nonneg (hc 0) (Real.exp_pos _).le
      linarith
  have hs : Summable (fun n : ℕ => c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t) :=
    summable_of_sum_range_le
      (fun n => div_nonneg (hc _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hbound
  exact (summable_nat_add_iff 1 (f := fun n : ℕ => c n / (n : ℝ) ^ t)).mp hs

end UpperTheory.V.Af.Rs
end
end

