module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentDivisorSumLe
section
open scoped BigOperators

namespace GlobalTheory

private lemma exponent_product_le_G_div_N_mul_rpow (f r : ℕ) (G N H Q l d : ℝ) (hG : 1 ≤ G) (hN : 1 ≤ N)
    (hGH : G ≤ H) (hNH : N ≤ H) (hQ : 0 ≤ Q) (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d)
    (hdG : d ≤ G) :
    (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
        (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) ≤
      G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0
  have hGdG : G / d ≤ G := div_le_self (by linarith) hd

  have h1 : (G / d) ^ (l + 3) ≤ G * H ^ (l + 2) := by
    rw [show l + 3 = 1 + (l + 2) by ring, Real.rpow_add hGd0, Real.rpow_one]
    exact mul_le_mul hGdG (Real.rpow_le_rpow hGd0.le (hGdG.trans hGH) (by linarith))
      (Real.rpow_nonneg hGd0.le _) (by linarith)

  have h2 : N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r + 2) := by
    have hN2 : N ^ (2 * r) ≤ H ^ (2 * r) := pow_le_pow_left₀ hN0.le hNH _
    calc N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r) * H * H :=
          mul_le_mul (mul_le_mul hN2 hNH hN0.le (pow_nonneg hH0.le _)) hQH
            (mul_nonneg hQ (by positivity)) (mul_nonneg (pow_nonneg hH0.le _) hH0.le)
      _ = H ^ (2 * r + 2) := by ring
  have h3 : G ^ r ≤ H ^ r := pow_le_pow_left₀ (by linarith) hGH r

  have hE : H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) =
      H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r * H ^ (9 + 9 * r + 16 * r ^ 2) := by
    rw [← Real.rpow_natCast H (2 * r + 2), ← Real.rpow_natCast H r,
      ← Real.rpow_natCast H (9 + 9 * r + 16 * r ^ 2), ← Real.rpow_add hH0, ← Real.rpow_add hH0,
      ← Real.rpow_add hH0, ← Real.rpow_add hH0]
    congr 1
    push_cast
    ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hN0, hE]
  have hP : 0 ≤ H ^ (11 + 3 * l) := Real.rpow_nonneg hH0.le _
  have hM : 0 ≤ N ^ (2 * r) * N * (Q * 9 ^ f) :=
    mul_nonneg (mul_nonneg (pow_nonneg hN0.le _) hN0.le) (mul_nonneg hQ (by positivity))
  have hA : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hH0.le _)) hP
  have hR : 0 ≤ G ^ r := pow_nonneg (by linarith) _
  have hS : 0 ≤ H ^ (9 + 9 * r + 16 * r ^ 2) := pow_nonneg hH0.le _
  have hAM : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) :=
    mul_nonneg hA (pow_nonneg hH0.le _)
  calc (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) * N
        = (G / d) ^ (l + 3) * H ^ (11 + 3 * l) * (N ^ (2 * r) * N * (Q * 9 ^ f)) * G ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) := by ring
    _ ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h1 hP) h2 hM hA) h3 hR hAM) hS
    _ = G * (H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2)) := by ring

theorem exponent_term (k f r : ℕ) (G N H a Q l d : ℝ) (hk : 1 ≤ k)
    (hG : 1 ≤ G) (hN : 1 ≤ N) (hGH : G ≤ H) (hNH : N ≤ H) (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d) (hdG : d ≤ G) :
    (d / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * l)) *
        ((G / d) ^ ((k : ℝ) + (1 + l) + 1) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤
      H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0

  have hexp : ((m + 1 : ℕ) : ℝ) + (1 + l) + 1 = (m : ℝ) + (l + 3) := by push_cast; ring
  rw [hexp, Real.rpow_add hGd0, Real.rpow_natCast, Nat.add_sub_cancel, pow_succ]
  have hdm : (d / N) ^ m * (G / d) ^ m = (G / N) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hB := exponent_product_le_G_div_N_mul_rpow f r G N H Q l d hG hN hGH hNH hQ hQH hl hd hdG
  have hX : 0 ≤ a * (G / N) ^ m := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)
  calc (d / N) ^ m * a * (Q * H ^ (11 + 3 * l)) *
          ((G / d) ^ m * (G / d) ^ (l + 3) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)))
        = a * ((d / N) ^ m * (G / d) ^ m) * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by ring
    _ = a * (G / N) ^ m * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by rw [hdm]
    _ ≤ a * (G / N) ^ m * (G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hB hX
    _ = H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * ((G / N) ^ m * (G / N))) := by
          ring

theorem exponent_sum_le :
    ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  intro k f r G N H a Q C hk hr hf hlog hG hN hGH hNH ha hQ hQH hC
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl0 : 0 ≤ Real.logb 2 (f : ℝ) := Real.logb_nonneg one_lt_two hf1
  have h2f : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.logb 2 f := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith)), Real.logb_self_eq_one one_lt_two]
  have hX : 0 ≤ a * (G / N) ^ k := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)

  refine le_trans (Finset.sum_le_sum (g := fun _ =>
    H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k)) ?_) ?_
  · intro de hde
    rw [Finset.mem_Icc] at hde
    have hd1 : (1 : ℝ) ≤ de := by exact_mod_cast hde.1
    have hdG : (de : ℝ) ≤ G := le_trans (Nat.cast_le.mpr hde.2) (Nat.floor_le (by linarith))
    simp only [h2f]
    exact exponent_term k f r G N H a Q (Real.logb 2 f) de hk hG hN hGH hNH ha hQ hQH
      hl0 hd1 hdG
  ·
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hfl : (⌊G⌋₊ : ℝ) ≤ H := (Nat.floor_le (by linarith)).trans hGH
    have hsq : Real.sqrt r ≤ r := by
      have h0 := Real.sqrt_nonneg (r : ℝ)
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ r by linarith)
      nlinarith
    have hlog2 := Real.log_two_gt_d9
    have hlb : Real.logb 2 (f : ℝ) ≤ 7 / 4 * r := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by linarith)
        (show (0 : ℝ) ≤ Real.log 2 - 0.69 by linarith)]
    have hexp : 1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) ≤
        C * (r : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg (r : ℝ))]
    have hE0 : 0 ≤ H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) :=
      Real.rpow_nonneg hH0.le _
    calc (⌊G⌋₊ : ℝ) * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k))
        ≤ H * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k)) := mul_le_mul_of_nonneg_right hfl (mul_nonneg hE0 hX)
      _ = H ^ (1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) *
            (a * (G / N) ^ k) := by rw [Real.rpow_add hH0 1, Real.rpow_one]; ring
      _ ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) hX

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendAeLinearOfLocalSqBoundDense
section
open MeasureTheory

namespace GlobalTheory

theorem lintegral_enorm_sq_Lp {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (f : Lp E 2 ν) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
    (Lp.aestronglyMeasurable f)
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem eLpNorm_two_le_of_lintegral {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (g : Q → E) (B : ℝ) (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm' g 2 ν ≤ ENNReal.ofReal B := by
  have e := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (f := g) (μ := ν) (q := 2) (by norm_num)
  simp only [ENNReal.rpow_ofNat] at e
  have e := e.symm
  rw [← e, ENNReal.ofReal_pow hB] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem extend_ae_linear_of_local_sq : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : Submodule ℂ H), Dense (D : Set H) → ∀ F : H → X → E,
    (∀ u ∈ D, ∀ u' ∈ D, F (u + u') =ᵐ[μ] fun x => F u x + F u' x) →
    (∀ (b : ℂ), ∀ u ∈ D, F (b • u) =ᵐ[μ] fun x => b • F u x) →
    (∀ n, ∃ C : ℝ, ∀ u ∈ D, AEStronglyMeasurable (F u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖F u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    ∃ T : H → X → E, (∀ u ∈ D, T u = F u) ∧
      (∀ u u' : H, T (u + u') =ᵐ[μ] fun x => T u x + T u' x) ∧
      (∀ (b : ℂ) (u : H), T (b • u) =ᵐ[μ] fun x => b • T u x) ∧
      (∀ n, ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (T u) (μ.restrict (K n)) ∧
        ∫⁻ x in K n, (‖T u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) := by
  intro X _ μ K hK hcov H _ _ E _ _ _ D hD F hadd hsmul hbd
  classical
  choose C hC using hbd
  set w : ℕ → ℝ := fun n => (2:ℝ)⁻¹ ^ n / (1 + max (C n) 0) with hw
  have hwpos : ∀ n, 0 < w n := fun n =>
    div_pos (pow_pos (by norm_num) n) (by have := le_max_right (C n) 0; linarith)
  have hw0 : ∀ n, ENNReal.ofReal (w n) ≠ 0 := fun n => by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hwpos n
  set ν : Measure X := Measure.sum (fun n => ENNReal.ofReal (w n) • μ.restrict (K n)) with hν
  have hint : ∀ f : X → ENNReal,
      ∫⁻ x, f x ∂ν = ∑' n, ENNReal.ofReal (w n) * ∫⁻ x in K n, f x ∂μ := by
    intro f
    rw [hν, lintegral_sum_measure]
    congr 1; funext n
    rw [lintegral_smul_measure, smul_eq_mul]
  have hνμ : ν ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      measure_mono_null Set.inter_subset_left h0, mul_zero]
  have hμν : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs, ENNReal.tsum_eq_zero] at h0
    have h1 : ∀ n, μ (s ∩ K n) = 0 := fun n => by
      have := h0 n
      rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (hw0 n)
    have : s = ⋃ n, s ∩ K n := by rw [← Set.inter_iUnion, hcov, Set.inter_univ]
    rw [this]; exact measure_iUnion_null h1
  have hsq : ∀ u ∈ D, ∫⁻ x, ‖F u x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((Real.sqrt 2 * ‖u‖) ^ 2) := by
    intro u hu
    rw [hint]
    have hB : (Real.sqrt 2 * ‖u‖) ^ 2 = ∑' n : ℕ, (2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2 := by
      rw [tsum_mul_right, tsum_geometric_inv_two, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [hB, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    have h2 : ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C n * ‖u‖ ^ 2) := (hC n u hu).2
    have hM : 0 ≤ max (C n) 0 := le_max_right _ _
    calc ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (w n) * ENNReal.ofReal (max (C n) 0 * ‖u‖ ^ 2) := by
          gcongr
          exact h2.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
      _ = ENNReal.ofReal (w n * (max (C n) 0 * ‖u‖ ^ 2)) := (ENNReal.ofReal_mul (hwpos n).le).symm
      _ ≤ ENNReal.ofReal ((2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hw]
          simp only
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) n) (sq_nonneg ‖u‖)]
  have hae : ∀ u ∈ D, AEStronglyMeasurable (F u) ν := fun u hu =>
    aestronglyMeasurable_sum_measure_iff.2 fun n => (hC n u hu).1.smul_measure _
  have hmem : ∀ u ∈ D, MemLp (F u) 2 ν := by
    intro u hu
    have hb : eLpNorm (F u) 2 ν ≤ ENNReal.ofReal (Real.sqrt 2 * ‖u‖) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (hae u hu)]
      exact eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u hu)
    exact hb.trans_lt ENNReal.ofReal_lt_top
  let L : D →ₗ[ℂ] Lp E 2 ν :=
    { toFun := fun u => (hmem u u.2).toLp (F u)
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hadd u u.2 v v.2))
      map_smul' := fun b u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hsmul b u u.2)) }
  have hL : ∀ u (hu : u ∈ D), L ⟨u, hu⟩ = (hmem u hu).toLp (F u) := fun _ _ => rfl
  have hLb : ∃ c, ∀ u : D, ‖L u‖ ≤ c * ‖D.subtype u‖ := by
    refine ⟨Real.sqrt 2, fun u => ?_⟩
    rw [show L u = (hmem u u.2).toLp (F u) from rfl, Lp.norm_toLp]
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (hae u u.2)]
    exact eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u u.2)
  have hdense : DenseRange D.subtype := hD.denseRange_val
  set Ext : H →L[ℂ] Lp E 2 ν := L.extendOfNorm D.subtype with hExtdef
  have hExt : ∀ u (hu : u ∈ D), Ext u = (hmem u hu).toLp (F u) := fun u hu => by
    rw [← hL u hu]
    exact LinearMap.extendOfNorm_eq hdense hLb ⟨u, hu⟩
  let T : H → X → E := fun u => if u ∈ D then F u else ⇑(Ext u)
  have hTae : ∀ u, T u =ᵐ[ν] Ext u := by
    intro u
    by_cases hu : u ∈ D
    · simp only [T, if_pos hu]
      rw [hExt u hu]
      exact (MemLp.coeFn_toLp _).symm
    · simp only [T, if_neg hu]
      rfl
  have hres : ∀ n, μ.restrict (K n) ≪ ν := fun n =>
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hμν
  refine ⟨T, fun u hu => if_pos hu, fun u u' => ?_, fun b u => ?_, fun n => ?_⟩
  · refine hμν.ae_le ?_
    filter_upwards [hTae (u + u'), hTae u, hTae u', Lp.coeFn_add (Ext u) (Ext u')]
      with x h1 h2 h3 h4
    rw [h1, map_add (f := _), h4, Pi.add_apply, ← h2, ← h3]
  · refine hμν.ae_le ?_
    filter_upwards [hTae (b • u), hTae u, Lp.coeFn_smul b (Ext u)] with x h1 h2 h4
    rw [h1, map_smul, h4, Pi.smul_apply, ← h2]
  · refine ⟨‖Ext‖ ^ 2 / w n, fun u => ⟨?_, ?_⟩⟩
    · exact ((Lp.aestronglyMeasurable (Ext u)).congr (hTae u).symm).mono_ac (hres n)
    · have e1 : ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ = ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ :=
        lintegral_congr_ae ((hres n).ae_le ((hTae u).mono fun x hx => by simp only [hx]))
      have e2 : ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) := by
        calc _ ≤ ∑' m, ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ :=
              ENNReal.le_tsum (f := fun m => ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ) n
          _ = ∫⁻ x, ‖Ext u x‖ₑ ^ 2 ∂ν := (hint _).symm
          _ = ENNReal.ofReal (‖Ext u‖ ^ 2) := lintegral_enorm_sq_Lp ν _
          _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (Ext.le_opNorm u) 2
      have hd : ENNReal.ofReal (‖Ext‖ ^ 2 / w n * ‖u‖ ^ 2)
          = ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) / ENNReal.ofReal (w n) := by
        rw [← ENNReal.ofReal_div_of_pos (hwpos n)]
        congr 1; ring
      change ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ ≤ _
      rw [e1, hd, ENNReal.le_div_iff_mul_le (Or.inl (hw0 n)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact e2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodEqProdMulFinprodIte
section
namespace GlobalTheory.FinprodProdMulIte


open Classical in
theorem finprod_eq_prod_mul_finprod_ite {ι : Type} (S₁ : Finset ι) (f g : ι → ℂ)
    (hf : (Function.mulSupport f).Finite) (hfg : ∀ p, p ∉ S₁ → f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S₁, f p) * ∏ᶠ p, (if p ∈ S₁ then (1 : ℂ) else g p) := by
  have hsub₁ : Function.mulSupport (fun p => if p ∈ S₁ then f p else (1 : ℂ)) ⊆ (S₁ : Set ι) := by
    intro p hp
    by_contra h
    have h' : p ∉ S₁ := h
    exact hp (by simp [h'])
  have hsub₂ : Function.mulSupport (fun p => if p ∈ S₁ then (1 : ℂ) else g p)
      ⊆ Function.mulSupport f := by
    intro p hp
    by_cases h : p ∈ S₁
    · exact absurd (by simp [h]) hp
    · intro h1
      exact hp (by simp [h, ← hfg p h, h1])
  have h₁ : ∏ᶠ p, (if p ∈ S₁ then f p else (1 : ℂ)) = ∏ p ∈ S₁, f p := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub₁]
    exact Finset.prod_congr rfl fun p hp => by simp [hp]
  rw [← h₁, ← finprod_mul_distrib (S₁.finite_toSet.subset hsub₁) (hf.subset hsub₂)]
  refine finprod_congr fun p => ?_
  by_cases h : p ∈ S₁
  · simp [h]
  · simp [h, hfg p h]

end GlobalTheory.FinprodProdMulIte
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
section
open Filter Topology

namespace GlobalTheory

open Filter Topology in
private theorem norm_update_sub_update_sub_smul_le {k : ℕ} (F : (Fin k → ℝ) → ℂ)
    (d : Fin k → (Fin k → ℝ) → ℂ)
    (hF : ∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i))
    (i : Fin k) (t y : Fin k → ℝ) {ε δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ z, dist z t < δ → ‖d i z - d i t‖ ≤ ε) (hy : dist y t < δ) {a b : ℝ}
    (ha : dist a (t i) < δ) (hb : dist b (t i) < δ) :
    ‖F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t‖ ≤ ε * |b - a| := by
  set g : ℝ → ℂ := fun s => F (Function.update y i s) - s • d i t with hg
  have hmem : ∀ s ∈ Metric.ball (t i) δ, dist (Function.update y i s) t < δ := by
    intro s hs
    rw [dist_pi_lt_iff hδ]
    intro m
    by_cases hm : m = i
    · subst hm
      simpa using hs
    · rw [Function.update_of_ne hm]
      exact lt_of_le_of_lt (dist_le_pi_dist y t m) hy
  have hderiv : ∀ s ∈ Metric.ball (t i) δ,
      HasDerivWithinAt g (d i (Function.update y i s) - d i t) (Metric.ball (t i) δ) s := by
    intro s _
    have h1 := hF i (Function.update y i s)
    simp only [Function.update_idem, Function.update_self] at h1
    have h2 : HasDerivAt (fun u : ℝ => u • d i t) ((1 : ℝ) • d i t) s :=
      (hasDerivAt_id s).smul_const (d i t)
    rw [one_smul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Metric.ball (t i) δ, ‖d i (Function.update y i s) - d i t‖ ≤ ε :=
    fun s hs => hgood _ (hmem s hs)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_ball (t i) δ) (Metric.mem_ball.2 ha) (Metric.mem_ball.2 hb)
  have hdiff : g b - g a = F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t := by
    simp only [hg, sub_smul]
    abel
  rw [hdiff, Real.norm_eq_abs] at key
  exact key


open Filter Topology in
theorem _root_.GlobalTheory.hasFDerivAt_of_continuous_partials :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  intro k F d hF hd t
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / (k + 1) with hε
  have hεpos : 0 < ε := div_pos hc (by positivity)
  have hev : ∀ᶠ z in 𝓝 t, ∀ i, dist (d i z) (d i t) < ε :=
    eventually_all.2 fun i => (hd i).continuousAt.eventually (Metric.ball_mem_nhds (d i t) hεpos)
  obtain ⟨δ, hδ, hδgood⟩ := Metric.eventually_nhds_iff.1 hev
  have hgood : ∀ i z, dist z t < δ → ‖d i z - d i t‖ ≤ ε := fun i z hz =>
    (dist_eq_norm (d i z) (d i t) ▸ (hδgood hz i)).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh
  set p : ℕ → (Fin k → ℝ) := fun j m => if (m : ℕ) < j then t m + h m else t m with hp
  set a : ℕ → ℂ := fun j => if hj : j < k then h ⟨j, hj⟩ • d ⟨j, hj⟩ t else 0 with ha
  have hp0 : p 0 = t := by
    funext m
    simp [hp]
  have hpk : p k = t + h := by
    funext m
    simp [hp, m.isLt]
  have hsumL : (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h =
      ∑ j ∈ Finset.range k, a j := by
    rw [Finset.sum_range]
    simp [ha, ContinuousLinearMap.sum_apply]
  have htel : F (t + h) - F t = ∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j)) := by
    rw [Finset.sum_range_sub (fun j => F (p j)) k, hpk, hp0]
  have hpdist : ∀ j, dist (p j) t < δ := by
    intro j
    rw [dist_pi_lt_iff hδ]
    intro m
    simp only [hp]
    split_ifs
    · rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h m) hh
    · simpa using hδ
  have hstep : ∀ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ ≤ ε * ‖h‖ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set i : Fin k := ⟨j, hjk⟩ with hi
    have haj : a j = ((t i + h i) - t i) • d i t := by
      simp [ha, hjk, hi]
    have hnext : p (j + 1) = Function.update (p j) i (t i + h i) := by
      funext m
      by_cases hm : m = i
      · subst hm
        simp [hp, hi]
      · have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext e)
        rw [Function.update_of_ne hm]
        simp only [hp]
        have : (m : ℕ) < j + 1 ↔ (m : ℕ) < j := by omega
        simp only [this]
    have hcur : p j = Function.update (p j) i (t i) := by
      symm
      rw [Function.update_eq_self_iff]
      simp [hp, hi]
    have hx : dist (t i + h i) (t i) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h i) hh
    have hmain := norm_update_sub_update_sub_smul_le F d hF i t (p j) hδ (hgood i) (hpdist j)
      (a := t i) (b := t i + h i) (by rw [dist_self]; exact hδ) hx
    rw [haj, hnext]
    conv_lhs => rw [hcur]
    rw [Function.update_idem]
    refine hmain.trans ?_
    gcongr
    rw [add_sub_cancel_left]
    simpa using norm_le_pi_norm h i
  calc ‖F (t + h) - F t - (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h‖
      = ‖∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j) - a j)‖ := by
        rw [hsumL, htel, ← Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ε * ‖h‖ := Finset.sum_le_sum hstep
    _ = k * (ε * ‖h‖) := by simp
    _ ≤ c * ‖h‖ := by
        rw [← mul_assoc]
        gcongr
        rw [hε, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end GlobalTheory
end

