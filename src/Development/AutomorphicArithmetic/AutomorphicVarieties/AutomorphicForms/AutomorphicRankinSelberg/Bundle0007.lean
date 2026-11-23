module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Unfold
section
open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

namespace UpperTheory.V.Af.Rs

private theorem unf_meas_strip : MeasurableSet strip := by
  unfold strip
  exact (measurableSet_le measurable_const UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_lt UpperHalfPlane.continuous_re.measurable measurable_const)

private theorem unf_meas_smul (γ : SL(2, ℤ)) : Measurable (fun z : ℍ => γ • z) := by
  refine Continuous.measurable ?_
  rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
  have h : (UpperHalfPlane.coe ∘ fun z : ℍ => γ • z) = fun z : ℍ =>
      (((algebraMap ℤ ℝ (γ 0 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 0 1) : ℂ)) /
      ((algebraMap ℤ ℝ (γ 1 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 1 1) : ℂ))) :=
    funext fun z => UpperHalfPlane.coe_specialLinearGroup_apply γ z
  rw [h]
  refine Continuous.div₀ (by fun_prop) (by fun_prop) fun z => ?_
  have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  simpa [UpperHalfPlane.denom] using this

private theorem unf_countable : Countable SL(2, ℤ) := @Subtype.countable (Matrix (Fin 2) (Fin 2) ℤ) (show Countable (Fin 2 → Fin 2 → ℤ) from inferInstance) _

end UpperTheory.V.Af.Rs

private theorem hasSum_integral_fd_smul_eq_two_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hU : UpperTheory.V.Af.Rs.UnfM) (f : ℍ → E) (hfm : StronglyMeasurable f)
    (hfi : Integrable f volume) :
    HasSum (fun γ : SL(2, ℤ) => ∫ z in ModularGroup.fd, f (γ • z)) ((2 : ℝ) • ∫ z, f z) := by
  have hsum : Integrable f (Measure.sum fun γ : SL(2, ℤ) =>
      Measure.map (fun z => γ • z) (volume.restrict ModularGroup.fd)) := by
    rw [hU, two_smul]
    exact hfi.add_measure hfi
  have h1 := hasSum_integral_measure hsum
  rw [hU, two_smul, integral_add_measure hfi hfi, ← two_smul ℝ] at h1
  convert h1 using 1
  funext γ
  rw [integral_map (UpperTheory.V.Af.Rs.unf_meas_smul γ).aemeasurable hfm.aestronglyMeasurable]

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.unfold :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.UnfM → UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.Unfold := by
  classical
  intro _ hU hR H Φ hH hHi hHΦ hΦ
  haveI := unf_countable
  have hstrip := unf_meas_strip
  set f : ℍ → ℂ := strip.indicator H with hf
  have hfm : StronglyMeasurable f := hH.stronglyMeasurable.indicator hstrip
  have hfi : Integrable f volume := (integrable_indicator_iff hstrip).mpr hHi
  have hA := hasSum_integral_fd_smul_eq_two_integral hU f hfm hfi
  have hB := hasSum_integral_fd_smul_eq_two_integral hU (fun z => ‖f z‖) hfm.norm hfi.norm
  have hval : (2 : ℝ) • ∫ z, f z = 2 * ∫ z in strip, H z := by
    rw [hf, integral_indicator hstrip]
    norm_num
  rw [hval] at hA
  have hfγ : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = if γ • z ∈ strip then Φ (row γ) z else 0 := by
    intro γ z
    rw [hf]
    split_ifs with h
    · rw [indicator_of_mem h, hHΦ]
    · rw [indicator_of_notMem h]
  let g : SL(2, ℤ) → Cop := fun γ => ⟨row γ, hR.1 γ⟩
  have hA' := (Equiv.sigmaFiberEquiv g).hasSum_iff.mpr hA
  refine HasSum.sigma hA' fun x => ?_
  have hint : ∀ c : {γ // g γ = x},
      Integrable (fun z => f (c.1 • z)) (volume.restrict ModularGroup.fd) := by
    intro c
    refine Integrable.mono (hΦ x)
      ((hfm.comp_measurable (unf_meas_smul c.1)).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    have hrow : row c.1 = x := congrArg Subtype.val c.2
    rw [hfγ]
    split_ifs
    · rw [hrow]
    · simp
  have hsumm : Summable fun c : {γ // g γ = x} => ∫ z in ModularGroup.fd, ‖f (c.1 • z)‖ :=
    hB.summable.comp_injective Subtype.val_injective
  have h := hasSum_integral_of_summable_integral_norm hint hsumm
  have heq : ∀ z, ∑' c : {γ // g γ = x}, f (c.1 • z) = Φ x z := by
    intro z
    obtain ⟨γ0, ⟨h0row, h0s⟩, huniq⟩ := hR.2 z x
    have hg0 : g γ0 = x := Subtype.ext h0row
    rw [tsum_eq_single ⟨γ0, hg0⟩]
    · rw [hfγ, if_pos h0s, h0row]
    · intro c hc
      rw [hfγ, if_neg]
      intro hs
      apply hc
      exact Subtype.ext (huniq c.1 ⟨congrArg Subtype.val c.2, hs⟩)
  simp only [heq] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolMap
section
noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private lemma measurable_ofComplex : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw), ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id measurable_const

private lemma pt_eq (p : ℝ × ℝ) : pt p.1 p.2 = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold pt
  congr 1
  apply Complex.ext <;> simp

theorem volMap : VolMap := by
  have hm : Measurable (fun p : ℝ × ℝ => pt p.1 p.2) := by
    simp only [pt_eq]
    exact measurable_ofComplex.comp Complex.measurableEquivRealProd.symm.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' s ∩ univ ×ˢ Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_image, pt_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

end UpperTheory.V.Af.Rs
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ZInt
section
open MeasureTheory Set UpperHalfPlane

theorem UpperTheory.V.Af.Rs.zInt :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZInt := by
  intro hF hB hW L _ G hG s hs v v'
  obtain ⟨hGc, C0, hC0⟩ := hG
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨h1, h2, -, -, -, h6⟩ := hB s hs'
  have hW2 : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  set W := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * s)) with hWdef
  set g : (Fin 2 → ℤ) → ℍ → ℝ := fun x z =>
    if UpperTheory.V.Af.Rs.cls L x = v' then UpperTheory.V.Af.Rs.ker s x z else 0 with hg
  have hg0 : ∀ x z, 0 ≤ g x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [h2 x z, le_rfl]
  have hgle : ∀ x z, g x z ≤ UpperTheory.V.Af.Rs.ker s x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [le_rfl, h2 x z]
  have hgm : ∀ x, Measurable (g x) := by
    intro x
    by_cases h : UpperTheory.V.Af.Rs.cls L x = v'
    · have e : g x = UpperTheory.V.Af.Rs.ker s x := by
        funext z
        simp [hg, h]
      rw [e]
      exact (h1 x).measurable
    · have e : g x = fun _ => 0 := by
        funext z
        simp [hg, h]
      rw [e]
      exact measurable_const
  have hgs : ∀ z ∈ ModularGroup.fd, Summable fun x => g x z := fun z hz =>
    Summable.of_nonneg_of_le (fun x => hg0 x z) (fun x => (hgle x z).trans (h6 x z hz))
      (hW2.mul_left _)
  have hEq : EqOn (fun z => G v z * (((∑' x, ENNReal.ofReal (g x z)).toReal : ℝ) : ℂ))
      (fun z => G v z * ((UpperTheory.V.Af.Rs.Zc L v' s z : ℝ) : ℂ)) ModularGroup.fd := by
    intro z hz
    have e : (∑' x, ENNReal.ofReal (g x z)).toReal = UpperTheory.V.Af.Rs.Zc L v' s z := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => hg0 x z) (hgs z hz),
        ENNReal.toReal_ofReal (tsum_nonneg fun x => hg0 x z)]
      rfl
    simp only [e]
  refine IntegrableOn.congr_fun ?_ hEq hF.1
  refine Measure.integrableOn_of_bounded (M := 8 * C0 * W) hF.2.ne ?_ ?_
  · exact ((hGc v).measurable.mul (Complex.measurable_ofReal.comp
      (Measurable.ennreal_toReal (Measurable.tsum fun x => (hgm x).ennreal_ofReal)))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem hF.1 fun z hz => ?_
    have him0 : 0 < z.im := z.im_pos
    have him : 1 / 2 ≤ z.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      nlinarith
    have e := hEq hz
    simp only at e
    rw [e]
    have hZ0 : 0 ≤ UpperTheory.V.Af.Rs.Zc L v' s z := tsum_nonneg fun x => hg0 x z
    have hZ : UpperTheory.V.Af.Rs.Zc L v' s z ≤ 4 * z.im ^ 2 * W := by
      calc UpperTheory.V.Af.Rs.Zc L v' s z = ∑' x, g x z := rfl
        _ ≤ ∑' x : Fin 2 → ℤ, 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) :=
          Summable.tsum_le_tsum (fun x => (hgle x z).trans (h6 x z hz)) (hgs z hz) (hW2.mul_left _)
        _ = 4 * z.im ^ 2 * W := tsum_mul_left
    have hGb := hC0 v z him
    have hW0 : 0 ≤ W := tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hZ0]
    have hG2 : ‖G v z‖ * z.im ^ 2 ≤ 2 * C0 := by
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (G v z)) (sq_nonneg z.im)) (sub_nonneg.mpr him)]
    calc ‖G v z‖ * UpperTheory.V.Af.Rs.Zc L v' s z ≤ ‖G v z‖ * (4 * z.im ^ 2 * W) :=
          mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
      _ ≤ 8 * C0 * W := by nlinarith [mul_le_mul_of_nonneg_left hG2 hW0]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ZLow
section
theorem UpperTheory.V.Af.Rs.zLow :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerLow → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZLow := by
  intro hB hL hW L _ s hs z hz
  have hs' : s ∈ Set.Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h0, -, -, -, hub⟩ := hB s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  have hk : Summable fun x : Fin 2 → ℤ => UpperTheory.V.Af.Rs.ker s x z :=
    Summable.of_nonneg_of_le (fun x => h0 x z) (fun x => hub x z hz) (hsum.mul_left _)
  have hv : ∀ v ∈ (Finset.univ : Finset (Fin 2 → ZMod L)), Summable fun x : Fin 2 → ℤ =>
      if UpperTheory.V.Af.Rs.cls L x = v then UpperTheory.V.Af.Rs.ker s x z else 0 := by
    intro v _
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hk
    · split_ifs
      · exact h0 x z
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact h0 x z
  have he : ∑ v, UpperTheory.V.Af.Rs.Zc L v s z = ∑' x : Fin 2 → ℤ, UpperTheory.V.Af.Rs.ker s x z := by
    unfold UpperTheory.V.Af.Rs.Zc
    rw [← Summable.tsum_finsetSum hv]
    refine tsum_congr fun x => ?_
    simp
  rw [he, UpperTheory.V.Af.Rs.Wsum, ← tsum_mul_left]
  exact (hsum.mul_left _).tsum_le_tsum (fun x => hL s hs' x z hz) hk
end

