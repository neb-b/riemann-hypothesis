module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPolB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriUniq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QrMapMeasurableSetImage
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaarA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPol
section
noncomputable section

open Finset Matrix MeasureTheory Metric

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HPol

variable {n : ℕ}

theorem haar_pol_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (d : ℝ)
    (h : DensOn (fun S => μ (expSet S)) d) : DensOn (fun S => μ (polSet S)) d := by
  intro η hη
  set η' : ℝ := min (η / 3) (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hη'3 : η' ≤ η / 3 := min_le_left _ _
  obtain ⟨δ1, hδ1, hE⟩ := h η' hη'0
  obtain ⟨δ4, hδ4, hE2⟩ := h 2 (by norm_num)
  obtain ⟨δ2, hδ2, hI⟩ := HPol.image_est ε hη'0
  obtain ⟨δ3, hδ3, hP⟩ := HPol.polSet_eq_expSet ε
  refine ⟨min (min δ2 δ3) (min (δ1 / 2) (δ4 / 2)),
    lt_min (lt_min hδ2 hδ3) (lt_min (by positivity) (by positivity)), fun S hS hsmall => ?_⟩
  have hs2 : ∀ s ∈ S, ‖s‖ < δ2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_left _ _))
  have hs3 : ∀ s ∈ S, ‖s‖ < δ3 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : ∀ s ∈ S, ‖s‖ < δ1 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : ∀ s ∈ S, ‖s‖ < δ4 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hmeas, hnorm, hup, hlo⟩ := hI S hS hs2
  have hsm1 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ1 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs1 s hs
    linarith [hnorm s hs]
  have hsm4 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ4 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs4 s hs
    linarith [hnorm s hs]
  obtain ⟨hEu, hEl⟩ := hE _ hmeas hsm1
  beta_reduce at hEu hEl ⊢
  rw [hP S hs3]
  have hsq1 : (1 + η') * (1 + η') ≤ 1 + η := by nlinarith
  have hsq2 : 1 - η ≤ (1 - η') * (1 - η') := by nlinarith
  constructor
  · calc μ (expSet (HPol.Lm '' S)) ≤ ENNReal.ofReal ((1 + η') * d) * volume (HPol.Lm '' S) := hEu
      _ ≤ ENNReal.ofReal ((1 + η') * d) * (ENNReal.ofReal (1 + η') * volume S) := by gcongr
      _ = (ENNReal.ofReal ((1 + η') * d) * ENNReal.ofReal (1 + η')) * volume S := by
        rw [mul_assoc]
      _ ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
        gcongr
        rcases le_or_gt 0 d with hd | hd
        · rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc (1 + η') * d * (1 + η') = ((1 + η') * (1 + η')) * d := by ring
            _ ≤ (1 + η) * d := mul_le_mul_of_nonneg_right hsq1 hd
        · rw [ENNReal.ofReal_of_nonpos (by nlinarith), zero_mul]
          exact zero_le
  · rcases le_or_gt 0 d with hd | hd
    · calc ENNReal.ofReal ((1 - η) * d) * volume S
          ≤ (ENNReal.ofReal ((1 - η') * d) * ENNReal.ofReal (1 - η')) * volume S := by
            gcongr
            rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) hd)]
            apply ENNReal.ofReal_le_ofReal
            calc (1 - η) * d ≤ ((1 - η') * (1 - η')) * d := mul_le_mul_of_nonneg_right hsq2 hd
              _ = (1 - η') * d * (1 - η') := by ring
        _ = ENNReal.ofReal ((1 - η') * d) * (ENNReal.ofReal (1 - η') * volume S) := by
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal ((1 - η') * d) * volume (HPol.Lm '' S) := by gcongr
        _ ≤ μ (expSet (HPol.Lm '' S)) := hEl
    ·
      obtain ⟨hE2u, hE2l⟩ := hE2 _ hmeas hsm4
      beta_reduce at hE2u hE2l
      have h3 : ENNReal.ofReal ((1 + 2) * d) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
      rw [h3, zero_mul] at hE2u
      have h0 : ENNReal.ofReal ((1 - 2) * d) * volume (HPol.Lm '' S) = 0 :=
        le_antisymm (hE2l.trans hE2u) (zero_le)
      have hpos : ENNReal.ofReal ((1 - 2) * d) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvL : volume (HPol.Lm '' S) = 0 := (mul_eq_zero.mp h0).resolve_left hpos
      rw [hvL] at hlo
      have hpos' : ENNReal.ofReal (1 - η') ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvS : volume S = 0 :=
        (mul_eq_zero.mp (le_antisymm hlo (zero_le))).resolve_left hpos'
      rw [hvS, mul_zero]
      exact zero_le

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaar
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.QRH

variable {N : ℕ}

theorem qr_lintegral (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
  haveI hcpt : CompactSpace (UNgrp N) := by
    by_contra hnc
    rw [not_compactSpace_iff] at hnc
    have h1 := MeasureTheory.measure_univ_of_isMulLeftInvariant μ
    rw [measure_univ] at h1
    exact ENNReal.one_ne_top h1
  obtain ⟨c, hct, hkap⟩ := kap_eq (N := N)
  haveI : SigmaFinite (triMeas N) := by
    unfold triMeas triDens
    infer_instance
  haveI : SigmaFinite (kap N) := by
    rw [hkap]
    lift c to NNReal using hct
    show SigmaFinite (c • triMeas N)
    infer_instance
  have hprod := nuQR_eq_prod (N := N) μ
  have hcd : Continuous fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det :=
    Continuous.matrix_det (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)
  have hdet : Measurable fun Z : Fin N → Fin N → ℂ => ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) :=
    ((hcd.norm.pow _).measurable).ennreal_ofReal
  have hgm : Measurable (gmDens N) := by
    have he : gmDens N = fun Z => ENNReal.ofReal ((‖(Matrix.of Z).det‖ ^ (2 * N))⁻¹) := by
      funext Z
      unfold gmDens
      rw [_root_.zpow_neg, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [he]
    exact ((hcd.norm.pow _).measurable.inv).ennreal_ofReal
  have htd : Measurable (triDens (N := N)) := by
    unfold triDens
    first
    | fun_prop
    | measurability
  have key : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = c * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
    intro f hf
    have hg : Measurable fun Z => f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) := hf.mul hdet
    have hgq : Measurable fun p : UNgrp N × TriCo N =>
        f (qrMap p) * ENNReal.ofReal (‖(Matrix.of (qrMap p)).det‖ ^ (2 * N)) := hg.comp measurable_qrMap
    have s1 : ∫⁻ Z, f Z = ∫⁻ Z in glSet N, f Z := by
      rw [← lintegral_add_compl f (measurableSet_glSet (N := N))]
      have hc : (glSet N)ᶜ = {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det = 0} := by
        ext Z
        simp [glSet]
      rw [hc, setLIntegral_measure_zero _ _ volume_det_eq_zero, add_zero]
    have s2 : ∫⁻ Z in glSet N, f Z =
        ∫⁻ Z, f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) ∂((gmMeas N).restrict (glSet N)) := by
      unfold gmMeas
      rw [restrict_withDensity measurableSet_glSet, lintegral_withDensity_eq_lintegral_mul _ hgm hg]
      apply setLIntegral_congr_fun measurableSet_glSet
      intro Z hZ
      simp only [Pi.mul_apply]
      rw [mul_comm (f Z), ← mul_assoc, gmDens_mul Z hZ, one_mul]
    rw [s1, s2, ← map_qrMap_nuQR, lintegral_map hg measurable_qrMap, ← hprod,
      lintegral_prod _ hgq.aemeasurable, ← lintegral_const_mul' _ _ hct]
    apply lintegral_congr
    intro k
    rw [hkap, lintegral_smul_measure]
    congr 1
    unfold triMeas
    rw [lintegral_withDensity_eq_lintegral_mul _ htd (by
      first
      | exact hgq.comp measurable_prodMk_left
      | exact hgq.comp measurable_prod_mk_left)]
    apply setLIntegral_congr_fun measurableSet_triPos
    intro t ht
    simp only [Pi.mul_apply]
    rw [d_qrMap k t ht, mul_comm, mul_assoc, mul_comm _ (triDens t), triDens_mul t ht]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := key (fun _ => 1) measurable_const
    rw [h0, zero_mul, lintegral_const, one_mul] at h1
    have hv : (volume : Measure (Fin N → Fin N → ℂ)) Set.univ ≠ 0 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro i _
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro j _
      exact isOpen_univ.measure_ne_zero volume Set.univ_nonempty
    exact hv h1
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, ?_⟩
  intro f hf
  rw [ENNReal.ofReal_toReal hct]
  exact key f hf

end ReciprocityTheory.ChartRestriction.DS
end
end

