module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HasCMByIsogenyOf
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)

namespace Formalism.L2.Th1.F

namespace CmBy

private lemma re_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).re = (m : ℝ) + (n : ℝ) / 2 := by
  simp [omegaK]
  ring

private lemma im_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).im = (n : ℝ) * Real.sqrt d / 2 := by
  simp [omegaK]
  ring

lemma normSq_omega (d : ℕ) (m n : ℤ) :
    Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d)
      = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4) := by
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  rw [Complex.normSq_apply, re_add_mul_omegaK, im_add_mul_omegaK]
  linear_combination ((n : ℝ) ^ 2 / 4) * hs

lemma ne_zero (d : ℕ) (hd : 0 < d) (m n : ℤ) (h : (m, n) ≠ (0, 0)) :
    (m : ℂ) + (n : ℂ) * omegaK d ≠ 0 := by
  intro h0
  have hre := re_add_mul_omegaK d m n
  have him := im_add_mul_omegaK d m n
  rw [h0, Complex.zero_re] at hre
  rw [h0, Complex.zero_im] at him
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hn : (n : ℝ) = 0 := by
    have h2 : (n : ℝ) * Real.sqrt d = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · linarith
  have hm : (m : ℝ) = 0 := by rw [hn] at hre; linarith
  have hn' : n = 0 := by exact_mod_cast hn
  have hm' : m = 0 := by exact_mod_cast hm
  exact h (by rw [hm', hn'])

end CmBy

theorem has_cm_stable : HasCMByStable := by
  intro d L hL m n
  refine ⟨?_, CmBy.normSq_omega d m n⟩
  intro w hw
  have h1 : omegaK d * w ∈ L.lattice := hL w hw
  have he : ((m : ℂ) + (n : ℂ) * omegaK d) * w = m • w + n • (omegaK d * w) := by
    simp only [zsmul_eq_mul]; ring
  rw [he]
  exact L.lattice.add_mem (L.lattice.smul_mem m hw) (L.lattice.smul_mem n h1)

theorem hasCMByScale_of (h : Homogeneity) : HasCMByScale := by
  intro d L c hc hL w hw
  have hmem := (h L c hc).1
  rw [hmem] at hw ⊢
  rw [show c⁻¹ * (omegaK d * w) = omegaK d * (c⁻¹ * w) by ring]
  exact hL _ hw

theorem cmPairHasCMBy_of (h : CmStable) : CmPairHasCMBy := by
  intro a b c d ha hd hdisc hb
  obtain ⟨k, hk⟩ := hb
  subst hk
  have hst := h a (2 * k + 1) c d ha hd hdisc (-k) 1
  have heq : omegaK d = ((-k : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * cmTheta (2 * k + 1) d := by
    simp only [omegaK, cmTheta]
    push_cast
    ring
  intro w hw
  rw [heq]
  exact hst w hw

theorem hasCMByIsogeny_of (hs : HasCMByStable) (he : KerRepsExist) (hc : KerRepsCard)
    (hf : IsogenyFormulaInstance) (h2 : QuasiPeriodConstIsogeny) : HasCMByIsogeny := by
  intro d L hL m n hmn hd
  have hα0 := CmBy.ne_zero d hd m n hmn
  obtain ⟨hms, hnorm⟩ := hs d L hL m n
  obtain ⟨S, hS⟩ := he L _ hα0 hms
  exact ⟨S, hS, (hc L _ S hα0 hms hS).trans hnorm, hf L _ S hα0 hms hS, h2 L _ S hα0 hms hS⟩

theorem jInvScale_of (h : Homogeneity) : JInvScale := by
  intro L c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := h L c hc
  simp only [Formalism.L2.Th1.CM.jInv, hg2, hg3]
  have hc12 : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have e1 : ((c ^ 4)⁻¹ * L.g₂) ^ 3 = (c ^ 12)⁻¹ * L.g₂ ^ 3 := by ring
  have e2 : ((c ^ 6)⁻¹ * L.g₃) ^ 2 = (c ^ 12)⁻¹ * L.g₃ ^ 2 := by ring
  rw [e1, e2, show (1728 : ℂ) * ((c ^ 12)⁻¹ * L.g₂ ^ 3) = (c ^ 12)⁻¹ * (1728 * L.g₂ ^ 3) by ring,
    show (c ^ 12)⁻¹ * L.g₂ ^ 3 - 27 * ((c ^ 12)⁻¹ * L.g₃ ^ 2)
      = (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) by ring,
    mul_div_mul_left _ _ hc12]

theorem has_cm_scale : HasCMByScale := hasCMByScale_of homogeneity

theorem cm_pair_has_cm : CmPairHasCMBy := cmPairHasCMBy_of cmStable

theorem hasCMByIsogeny_of' (hf : IsogenyFormulaInstance) : HasCMByIsogeny :=
  hasCMByIsogeny_of has_cm_stable kerRepsExist kerRepsCard hf quasiPeriodConstIsogeny

theorem j_invariant_scale : JInvScale := jInvScale_of homogeneity

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaScale
section
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)

namespace Formalism.L2.Th1.F

namespace Scale

open PowerSeries

theorem cW_eq {K : Type} [Field K] (g2 g3 : K) (k : ℕ) :
    cW g2 g3 k =
      if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
      if 4 ≤ k then
        3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
          ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
      else 0 := by
  unfold cW
  rw [Nat.strongRecOn_eq]
  split_ifs <;> rfl

theorem cW_scale {K : Type} [Field K] (g2 g3 lam : K) (k : ℕ) :
    cW (lam ^ 4 * g2) (lam ^ 6 * g3) k = lam ^ (2 * k) * cW g2 g3 k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_eq, cW_eq g2 g3 k]
    split_ifs with h2 h3 h4
    · subst h2; ring
    · subst h3; ring
    · rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.isLt
      rw [ih (m.val + 2) (by omega), ih (k - (m.val + 2)) (by omega)]
      have e : lam ^ (2 * k) = lam ^ (2 * (m.val + 2)) * lam ^ (2 * (k - (m.val + 2))) := by
        rw [← pow_add]; congr 1; omega
      rw [e]; ring
    · rw [mul_zero]

theorem cW_map {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (g2 g3 : K) (k : ℕ) :
    φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_eq, cW_eq (φ g2) (φ g3) k]
    split_ifs with h2 h3 h4
    · rw [map_div₀, map_ofNat]
    · rw [map_div₀, map_ofNat]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, map_div₀, map_mul, map_add (f := _), map_sub, map_mul, map_natCast, map_one, map_sum]
      simp only [map_ofNat]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.isLt
      rw [map_mul, ih (m.val + 2) (by omega), ih (k - (m.val + 2)) (by omega)]
    · exact map_zero φ

theorem wpNum_scale {K : Type} [Field K] (g2 g3 lam : K) :
    wpNum (lam ^ 4 * g2) (lam ^ 6 * g3) = rescale lam (wpNum g2 g3) := by
  ext n
  rw [coeff_rescale]
  unfold wpNum
  rw [coeff_mk, coeff_mk]
  split_ifs with h0 he
  · subst h0; simp
  · rw [cW_scale, Nat.two_mul_div_two_of_even he]
  · rw [mul_zero]

theorem wpDen_scale {K : Type} [Field K] (g2 g3 lam : K) :
    wpDen (lam ^ 4 * g2) (lam ^ 6 * g3) = rescale lam (wpDen g2 g3) := by
  ext n
  rw [coeff_rescale]
  unfold wpDen
  rw [coeff_mk, coeff_mk]
  split_ifs with h0 he
  · subst h0; simp
  · rw [cW_scale, Nat.two_mul_div_two_of_even he]; ring
  · rw [mul_zero]

theorem pOf_scale {K : Type} [Field K] (g2 g3 lam : K) :
    pOf (lam ^ 4 * g2) (lam ^ 6 * g3) = C (lam ^ 2) * rescale lam (pOf g2 g3) := by
  ext n
  rw [coeff_C_mul, coeff_rescale]
  unfold pOf
  rw [coeff_mk, coeff_mk, wpNum_scale, coeff_rescale]
  ring

theorem cc_wpDen {K : Type} [Field K] (g2 g3 : K) : constantCoeff (wpDen g2 g3) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  unfold wpDen
  rw [coeff_mk, if_pos rfl]

theorem rescale_inv {K : Type} [Field K] (lam : K) {f : PowerSeries K}
    (hf : constantCoeff f ≠ 0) : rescale lam f⁻¹ = (rescale lam f)⁻¹ := by
  have h1 : constantCoeff (rescale lam f) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
    exact hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h1, ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]

theorem uSer_scale {K : Type} [Field K] (g2 g3 lam : K) :
    C lam * uSer (lam ^ 4 * g2) (lam ^ 6 * g3) = rescale lam (uSer g2 g3) := by
  unfold uSer
  rw [map_mul, map_mul, rescale_X, rescale_inv lam (by rw [cc_wpDen]; exact one_ne_zero),
    wpNum_scale, wpDen_scale]
  ring

variable {K : Type} [Field K] [CharZero K]

theorem prim_scale (lam : K) (f : PowerSeries K) :
    Formalism.L2.Th1.B.prim (C lam * rescale lam f) = rescale lam (Formalism.L2.Th1.B.prim f) := by
  ext n
  rw [coeff_rescale]
  unfold Formalism.L2.Th1.B.prim
  rw [coeff_mk, coeff_mk]
  split_ifs with h0
  · rw [mul_zero]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [Nat.succ_sub_one, coeff_C_mul, coeff_rescale, pow_succ]
    ring

theorem prim_C_mul (a : K) (f : PowerSeries K) :
    Formalism.L2.Th1.B.prim (C a * f) = C a * Formalism.L2.Th1.B.prim f := by
  ext n
  rw [coeff_C_mul]
  unfold Formalism.L2.Th1.B.prim
  rw [coeff_mk, coeff_mk]
  split_ifs with h0
  · rw [mul_zero]
  · rw [coeff_C_mul, mul_div_assoc]

theorem sigS_scale (lam : K) (P : PowerSeries K) :
    Formalism.L2.Th1.B.sigS (C (lam ^ 2) * rescale lam P) = rescale lam (Formalism.L2.Th1.B.sigS P) := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, ← prim_scale, ← prim_scale, ← prim_C_mul, ← mul_assoc, ← map_mul, sq]

theorem sigma_scale (lam : K) (P : PowerSeries K) :
    C lam * Formalism.L2.Th1.B.sigma (C (lam ^ 2) * rescale lam P)
      = rescale lam (Formalism.L2.Th1.B.sigma P) := by
  unfold Formalism.L2.Th1.B.sigma
  rw [map_mul, rescale_X, Formalism.L2.Th1.B.Sq.rescale_fExp lam (Formalism.L2.Th1.B.Map.cc_sigS P),
    sigS_scale, mul_assoc]

theorem sgStar_scale (s lam : K) (P : PowerSeries K) :
    C lam * Formalism.L2.Th1.B.sgStar (lam ^ 2 * s) (C (lam ^ 2) * rescale lam P)
      = rescale lam (Formalism.L2.Th1.B.sgStar s P) := by
  unfold Formalism.L2.Th1.B.sgStar
  rw [map_mul, ← sigma_scale, Formalism.L2.Th1.B.Sq.rescale_fExp lam (by simp), mul_assoc]
  congr 3
  rw [map_neg, map_mul, map_pow, rescale_X, mul_pow, ← map_pow, ← mul_assoc]
  congr 2
  have hC : rescale lam (C (s / 2)) = C (s / 2) := by
    ext n
    rw [coeff_rescale, coeff_C]
    split_ifs with h0
    · subst h0; rw [pow_zero, one_mul]
    · rw [mul_zero]
  rw [hC, ← map_mul]
  congr 1
  ring

end Scale

theorem series_scale : SeriesScale := fun _ _ _ g2 g3 lam =>
  ⟨Scale.cW_scale g2 g3 lam, Scale.wpNum_scale g2 g3 lam, Scale.wpDen_scale g2 g3 lam,
    Scale.pOf_scale g2 g3 lam, Scale.uSer_scale g2 g3 lam⟩

theorem sigma_scale' : SigmaScale := fun _ _ _ P s lam =>
  ⟨Scale.sigma_scale lam P, Scale.sgStar_scale s lam P⟩

namespace Scale

open PowerSeries

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem wpNum_map (g2 g3 : K) : map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  rw [coeff_map]
  unfold wpNum
  rw [coeff_mk, coeff_mk]
  split_ifs
  · exact map_one φ
  · exact cW_map φ g2 g3 _
  · exact map_zero φ

theorem wpDen_map (g2 g3 : K) : map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  rw [coeff_map]
  unfold wpDen
  rw [coeff_mk, coeff_mk]
  split_ifs
  · exact map_one φ
  · rw [map_mul, map_neg, map_sub, map_natCast, map_one, cW_map]
  · exact map_zero φ

theorem pOf_map (g2 g3 : K) : map φ (pOf g2 g3) = pOf (φ g2) (φ g3) := by
  ext n
  rw [coeff_map]
  unfold pOf
  rw [coeff_mk, coeff_mk, ← wpNum_map, coeff_map]

theorem uSer_map [CharZero K] [CharZero K'] (g2 g3 : K) :
    map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  unfold uSer
  rw [map_mul, map_mul, map_X,
    Formalism.L2.Th1.B.Map.map_inv' φ (by rw [cc_wpDen]; exact one_ne_zero), wpNum_map, wpDen_map]

end Scale

theorem series_map : SeriesMap := fun _ _ _ _ _ _ φ g2 g3 s P =>
  ⟨Scale.wpNum_map φ g2 g3, Scale.wpDen_map φ g2 g3, Scale.pOf_map φ g2 g3,
    Scale.uSer_map φ g2 g3, Formalism.L2.Th1.B.Map.map_sigma φ P, Formalism.L2.Th1.B.Map.map_sgStar φ s P⟩

end Formalism.L2.Th1.F
end
end

