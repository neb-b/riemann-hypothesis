module

public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos
section
namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace

lemma hlin_vsq_pos {p : ℕ} {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < vsq g := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))

theorem perpTrace : PerpTraceStatement := by
  intro p g hg
  have hs := hlin_vsq_pos hg
  refine ⟨fun i => sub_nonneg.mpr ((div_le_one hs).mpr
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))), ?_⟩
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  change _ - vsq g / vsq g = _
  rw [div_self hs.ne']
  simp

end ReciprocityTheory.L2DbarEstimates.H
end

-- bundled from ReciprocityTheory.L2DbarEstimates.SkodaWeights.NeedBergmanClosed
section
namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates

def NeedBergmanClosed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ ψ : M → ℝ, Continuous ψ →
    IsClosed (holSub n z ψ : Set (WeightedL2 n z ψ))

end ReciprocityTheory.L2DbarEstimates.H
end

-- bundled from ReciprocityTheory.L2DbarEstimates.SkodaWeights.WeightedIntegralEqLintegral
section
namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

lemma measurable_exp_neg_density {M : Type*} [MeasurableSpace M] {ψ : M → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (-ψ x))) := (hψ.neg.exp).ennreal_ofReal

lemma ae_weighted_iff_ae (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (P : M → Prop) :
    (∀ᵐ x ∂wvol n z ψ, P x) ↔ ∀ᵐ x ∂vol n z, P x := by
  unfold wvol
  rw [ae_withDensity_iff (measurable_exp_neg_density hψ)]
  refine ⟨fun h => h.mono fun x hx => hx ?_, fun h => h.mono fun x hx _ => hx⟩
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma weightedIntegral_eq_lintegral (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    wint n z f ψ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂wvol n z ψ := by
  unfold wint wvol
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_exp_neg_density hψ)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.rpow_two,
    ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

lemma eLpNorm_two_weighted_eq (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    eLpNorm' f 2 (wvol n z ψ) = wint n z f ψ ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm'_eq_lintegral_eNorm, ← weightedIntegral_eq_lintegral n z hψ f]

theorem l2w (n : ℕ) (M : Type*) [MeasurableSpace M] : WeightedL2Properties n M := by
  intro z ψ hψ
  refine ⟨fun P => ae_weighted_iff_ae n z hψ P, fun F => ?_, fun f hf hfin => ?_⟩
  · have hlt := Lp.eLpNorm_lt_top F
    have hw : wint n z F ψ = eLpNorm F 2 (wvol n z ψ) ^ (2 : ℝ) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable F),
        ENNReal.toReal_ofNat, eLpNorm_two_weighted_eq n z hψ, ← ENNReal.rpow_mul]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [hw]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne
    · rw [hw, Lp.norm_def, ← ENNReal.toReal_rpow, Real.rpow_two]
  · have hmem : MemLp f 2 (wvol n z ψ) := by
      change eLpNorm f 2 (wvol n z ψ) < ⊤
      have hfw : AEStronglyMeasurable f (wvol n z ψ) :=
        hf.mono_ac (withDensity_absolutelyContinuous _ _)
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hfw, ENNReal.toReal_ofNat,
        eLpNorm_two_weighted_eq n z hψ f]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    exact ⟨hmem.toLp f, (ae_weighted_iff_ae n z hψ (fun x => (hmem.toLp f : M → ℂ) x = f x)).mp
      (MemLp.coeFn_toLp hmem)⟩

theorem volOpenPos (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    VolOpenPosStatement n M := by
  intro z hz U hU ⟨x, hx⟩
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  have hW : IsOpen (U ∩ e.source) := hU.inter e.open_source
  have hinj : Set.InjOn z e.source := by
    intro a ha b hb hab
    rw [he ha, he hb] at hab
    exact e.injOn ha hb hab
  have himg : z '' (U ∩ e.source) = e '' (U ∩ e.source) :=
    Set.image_congr fun y hy => he hy.2
  have hpos : 0 < volume (z '' (U ∩ e.source)) := by
    rw [himg]
    exact (e.isOpen_image_of_subset_source hW Set.inter_subset_right).measure_pos _
      ⟨e x, x, ⟨hx, hxe⟩, rfl⟩
  rw [← vol_image n z hz e.source e.open_source hinj _ hW.measurableSet
    Set.inter_subset_right] at hpos
  exact hpos.trans_le (measure_mono Set.inter_subset_left)

end ReciprocityTheory.L2DbarEstimates.H
end

