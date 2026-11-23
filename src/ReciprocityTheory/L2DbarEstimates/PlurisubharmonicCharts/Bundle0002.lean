module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeA
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal

noncomputable section

def apraW (d : ℕ) (ε τ : ℝ) (t : ℝ) : ℝ≥0∞ :=
  if t < ε then ENNReal.ofReal ((max (t ^ 2) τ) ^ (-(d : ℝ))) else 0

lemma apraW_meas (d : ℕ) (ε τ : ℝ) : Measurable (apraW d ε τ) := by
  unfold apraW
  refine Measurable.ite measurableSet_Iio ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp
    (((measurable_id.pow_const 2).max measurable_const).pow_const _)

lemma apraW_anti (d : ℕ) (ε : ℝ) {τ τ' : ℝ} (hτ : 0 < τ) (h : τ ≤ τ') (t : ℝ) :
    apraW d ε τ' t ≤ apraW d ε τ t := by
  unfold apraW
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_right hτ)
      (max_le_max le_rfl h) (neg_nonpos.mpr (Nat.cast_nonneg d)))
  · exact le_rfl

lemma apra_slice (d k : ℕ) (hMVd : MVStatement d) (ε τ : ℝ) (u : V d × V k → ℂ)
    (hu : DifferentiableOn ℂ u (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) (ζ : V k)
    (hζ : ζ ∈ ball (0 : V k) ε) :
    ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
      ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hdiff : DifferentiableOn ℂ (fun x : V d => u (x, ζ)) (ball 0 ε) :=
    hu.comp (differentiableOn_id.prodMk (differentiableOn_const ζ)) (fun x hx => ⟨hx, hζ⟩)
  have h := hMVd ε (fun x => u (x, ζ)) (apraW d ε τ) hdiff (apraW_meas d ε τ)
    (fun t ht => by simp [apraW, not_lt.mpr ht])
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun x => ?_
  by_cases hx : ‖x‖ < ε
  · have hx' : x ∈ ball (0 : V d) ε := mem_ball_zero_iff.mpr hx
    simp only [apraW, if_pos hx, Set.indicator_of_mem hx']
    rw [ENNReal.ofReal_mul (by positivity)]
  · have hx' : x ∉ ball (0 : V d) ε := fun h => hx (mem_ball_zero_iff.mp h)
    simp [apraW, hx]

lemma apra_base (k : ℕ) (hMVk : MVStatement k) (ε : ℝ) (g : V k → ℂ)
    (hg : DifferentiableOn ℂ g (ball 0 ε)) :
    ENNReal.ofReal (‖g 0‖ ^ 2) * volume (ball (0 : V k) ε) ≤
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
  have h := hMVk ε g (fun t => if t < ε then 1 else 0) hg
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)
    (fun t ht => by simp [not_lt.mpr ht])
  have e1 : ∫⁻ y : V k, (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      volume (ball (0 : V k) ε) := by
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  have e2 : ∫⁻ y : V k, ENNReal.ofReal (‖g y‖ ^ 2) *
      (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  rw [e1, e2] at h
  exact h

lemma apra_blow (d : ℕ) (hd : 1 ≤ d) (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) :
    ⨆ n : ℕ, ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
  have : Nontrivial (V d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  set f : ℕ → V d → ℝ≥0∞ := fun n x => apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ with hf
  have hmeas : ∀ n, Measurable (f n) := fun n => (apraW_meas _ _ _).comp measurable_norm
  have hmono : Monotone f := by
    intro m n hmn x
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    show apraW d ε (1 / ((m : ℝ) + 1)) ‖x‖ ≤ apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖
    exact apraW_anti d ε h2 h1 _
  rw [← lintegral_iSup hmeas hmono]
  set g : V d → ℝ≥0∞ := fun x => ENNReal.ofReal ‖x‖ ^ (-2 * (d : ℝ)) with hg
  have hpt : ∀ x : V d, x ≠ 0 → (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    intro x hx0
    by_cases hx : ‖x‖ < ε
    · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hx)]
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (pow_pos hpos 2)
      refine le_trans ?_ (le_iSup _ n)
      simp only [hf, hg, apraW, if_pos hx]
      rw [max_eq_left hn.le, ENNReal.ofReal_rpow_of_pos hpos, ← Real.rpow_natCast,
        ← Real.rpow_mul hpos.le]
      apply le_of_eq
      congr 2
      push_cast
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (mem_ball_zero_iff.mp h))]
      exact bot_le
  have hae : ∀ᵐ x ∂(volume : Measure (V d)), (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    have h0 : ∀ᵐ x ∂(volume : Measure (V d)), x ∉ ({0} : Set (V d)) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with x hx using hpt x (by simpa using hx)
  have hT : ∫⁻ y in ball (0 : V d) 1, g y = ⊤ :=
    not_lt_top_iff.mp (fun h => lt_irrefl _ ((hMVI hd d).1 h))
  have hdn : -2 * (d : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hpt2 : ∀ y : V d, g y ≤ (ball (0 : V d) ε).indicator g y + ENNReal.ofReal ε ^ (-2 * (d : ℝ)) := by
    intro y
    by_cases hy : y ∈ ball (0 : V d) ε
    · rw [Set.indicator_of_mem hy]
      exact le_self_add
    · rw [Set.indicator_of_notMem hy, zero_add]
      have : ε ≤ ‖y‖ := by simpa [mem_ball_zero_iff] using hy
      simp only [hg]
      rw [ENNReal.ofReal_rpow_of_pos (hε.trans_le this), ENNReal.ofReal_rpow_of_pos hε]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hε this hdn)
  have hc : ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [ENNReal.rpow_eq_top_iff, hε]) measure_ball_lt_top.ne
  have hle : ∫⁻ y in ball (0 : V d) 1, g y ≤ (∫⁻ y, (ball (0 : V d) ε).indicator g y) +
      ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
    calc ∫⁻ y in ball (0 : V d) 1, g y
        ≤ ∫⁻ y in ball (0 : V d) 1, ((ball (0 : V d) ε).indicator g y +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ))) := lintegral_mono fun y => hpt2 y
      _ = (∫⁻ y in ball (0 : V d) 1, (ball (0 : V d) ε).indicator g y) +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ _ := add_le_add (setLIntegral_le_lintegral _ _) le_rfl
  have hind : ∫⁻ y, (ball (0 : V d) ε).indicator g y = ⊤ := by
    by_contra hne
    exact (ENNReal.add_ne_top.2 ⟨hne, hc⟩) (eq_top_iff.2 (hT ▸ hle))
  exact eq_top_iff.2 (hind ▸ lintegral_mono_ae hae)

theorem ap_prod_blowup (d k : ℕ) (hd : 1 ≤ d) (hMVd : MVStatement d) (hMVk : MVStatement k)
    (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) (M : ℝ) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V d × V k → ℂ,
      DifferentiableOn ℂ u (Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε) →
      ENNReal.ofReal (M * ‖u 0‖ ^ 2) ≤
        ∫⁻ z in Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε,
          ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hvol : volume (ball (0 : V k) ε) ≠ 0 := (measure_ball_pos volume (0 : V k) hε).ne'
  have hsup : ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
    rw [← ENNReal.mul_iSup, apra_blow d hd hMVI ε hε, ENNReal.mul_top hvol]
  have hlt : ENNReal.ofReal M < ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ := by
    rw [hsup]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun τ hτ hτ0 u hu => ?_⟩
  have hIτ : ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ ≤ ∫⁻ x : V d, apraW d ε τ ‖x‖ :=
    lintegral_mono fun x => apraW_anti d ε hτ hτ0 _
  have hslice : ∀ ζ ∈ ball (0 : V k) ε,
      ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
        ∫⁻ x in ball (0 : V d) ε,
          ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) :=
    fun ζ hζ => apra_slice d k hMVd ε τ u hu ζ hζ
  have hbase := apra_base k hMVk ε (fun ζ => u (0, ζ))
    (hu.comp ((differentiableOn_const (0 : V d)).prodMk differentiableOn_id)
      (fun ζ hζ => ⟨mem_ball_self hε, hζ⟩))
  have hmeasF : AEMeasurable
      (fun z : V d × V k => ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))))
      ((volume.restrict (ball (0 : V d) ε)).prod (volume.restrict (ball (0 : V k) ε))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hu' : AEMeasurable u (volume.restrict (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) := by
      letI : IsBoundedSMul ℂ (V d × V k) := NormedSpace.toIsBoundedSMul
      letI : ContinuousSMul ℂ (V d × V k) := IsBoundedSMul.continuousSMul
      exact hu.continuousOn.aemeasurable (measurableSet_ball.prod measurableSet_ball)
    exact ((hu'.norm.pow_const 2).mul (((measurable_fst.norm.pow_const 2).max
      measurable_const).pow_const _).aemeasurable).ennreal_ofReal
  have hfub : ∫⁻ z in ball (0 : V d) ε ×ˢ ball (0 : V k) ε,
      ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) =
      ∫⁻ ζ in ball (0 : V k) ε, ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hmeasF]
  rw [hfub]
  calc ENNReal.ofReal (M * ‖u 0‖ ^ 2)
      = ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_mul' (by positivity), mul_comm]
        rfl
    _ ≤ ENNReal.ofReal (‖u (0, 0)‖ ^ 2) *
          (volume (ball (0 : V k) ε) * ∫⁻ x : V d, apraW d ε τ ‖x‖) :=
        mul_le_mul' le_rfl (hn.le.trans (mul_le_mul' le_rfl hIτ))
    _ = (ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * volume (ball (0 : V k) ε)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := (mul_assoc _ _ _).symm
    _ ≤ (∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := mul_le_mul' hbase le_rfl
    _ ≤ ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := lintegral_mul_const_le _ _
    _ ≤ _ := setLIntegral_mono' measurableSet_ball hslice

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
section
open Complex ComplexConjugate Filter Topology

namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative

open ReciprocityTheory.L2DbarEstimates

variable {n : ℕ}

theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} (hmax : IsLocalMax g 0)
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ g t) : deriv (deriv g) 0 ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hd2 : DifferentiableAt ℝ (deriv g) 0 := by
    by_contra hnd
    rw [deriv_zero_of_not_differentiableAt hnd] at hpos
    exact lt_irrefl _ hpos
  have h0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd2.hasDerivAt
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < slope (deriv g) 0 t := hslope.eventually (lt_mem_nhds hpos)
  rw [eventually_nhdsWithin_iff] at hev
  have hmax' : ∀ᶠ y in 𝓝 (0:ℝ), g y ≤ g 0 := hmax
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hev.and hd).and hmax')
  have ht : 0 < ε / 2 := half_pos hε
  have hdist : ∀ y ∈ Set.Icc (0:ℝ) (ε / 2), dist y 0 < ε := by
    intro y hy
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]
    linarith [hy.2]
  have hcont : ContinuousOn g (Set.Icc 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y hy)).1.2).continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ g (Set.Ioo 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y (Set.Ioo_subset_Icc_self hy))).1.2).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope g ht hcont hdiffOn
  have hcpos : 0 < deriv g c := by
    have h := (hball (hdist c (Set.Ioo_subset_Icc_self hc))).1.1
      (Set.mem_compl_singleton_iff.mpr hc.1.ne')
    simp only [slope_def_field, h0, sub_zero] at h
    exact (div_pos_iff_of_pos_right hc.1).mp h
  rw [hcd, sub_zero] at hcpos
  have hgt := (div_pos_iff_of_pos_right ht).mp hcpos
  have hle := (hball (hdist (ε / 2) ⟨ht.le, le_rfl⟩)).2
  linarith

private theorem differentiableAt_fderiv_of_contDiffAt_two' {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  (hf.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt (by norm_num)


set_option maxHeartbeats 400000 in
theorem snd_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (u : V n) : fderiv ℝ (fderiv ℝ f) x u u ≤ 0 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hγd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • u) u t := fun t => by
    simpa using ((hasDerivAt_id' t).smul_const u).const_add x
  have hγ : Tendsto (fun t : ℝ => x + t • u) (𝓝 0) (𝓝 x) := by
    have h := (hγd 0).continuousAt.tendsto
    simpa using h
  have hev := hγ.eventually (ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf)
  have hgd : ∀ t : ℝ, DifferentiableAt ℝ f (x + t • u) →
      HasDerivAt (fun t : ℝ => f (x + t • u)) (fderiv ℝ f (x + t • u) u) t :=
    fun t ht => ht.hasFDerivAt.comp_hasDerivAt t (hγd t)
  have hg : IsLocalMax (fun t : ℝ => f (x + t • u)) 0 := by
    show ∀ᶠ t in 𝓝 (0:ℝ), f (x + t • u) ≤ f (x + (0:ℝ) • u)
    filter_upwards [hγ.eventually (show ∀ᶠ y in 𝓝 x, f y ≤ f x from hmax)] with t ht
    simpa using ht
  have hdg : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ (fun t : ℝ => f (x + t • u)) t := by
    filter_upwards [hev] with t ht using (hgd t ht).differentiableAt
  have hEq : deriv (fun t : ℝ => f (x + t • u)) =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + t • u) u := by
    filter_upwards [hev] with t ht using (hgd t ht).deriv
  have hφ : HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) (x + (0:ℝ) • u) := by
    rw [zero_smul, add_zero]
    exact (hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).congr_fderiv (by ext b; simp)
  have h3 := hφ.comp_hasDerivAt (0:ℝ) (hγd 0)
  have h4 : ((fderiv ℝ (fderiv ℝ f) x).flip u) u = fderiv ℝ (fderiv ℝ f) x u u :=
    ContinuousLinearMap.flip_apply _ _ _
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • u) u) (fderiv ℝ (fderiv ℝ f) x u u) 0 := by
    rw [← h4]
    exact h3
  have h := deriv_deriv_nonpos_of_isLocalMax hg hdg
  rwa [hEq.deriv_eq, h2.deriv] at h

private theorem wirtinger_wirtingerBar_ofReal_lemma_2 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.wd n j (ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ))) x =
      (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hψ : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, HasFDerivAt (fun y => ((fderiv ℝ f y a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip a)) x := by
    intro a
    have h1 : HasFDerivAt (fun y => fderiv ℝ f y a) ((fderiv ℝ (fderiv ℝ f) x).flip a) x :=
      (hD.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).congr_fderiv (by ext b; simp)
    exact (Complex.ofRealCLM.hasFDerivAt.comp x h1).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  have hG : HasFDerivAt (fun y => (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)))
      ((2⁻¹ : ℂ) • (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (ReciprocityTheory.L2DbarEstimates.bas n k)) +
        I • Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (I • ReciprocityTheory.L2DbarEstimates.bas n k)))) x :=
    ((hψ (ReciprocityTheory.L2DbarEstimates.bas n k)).add ((hψ (I • ReciprocityTheory.L2DbarEstimates.bas n k)).const_mul I)).const_mul (2⁻¹ : ℂ)
  have hE : ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ)) =ᶠ[𝓝 x] fun y =>
      (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) := by
    filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
    rw [ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, div_eq_inv_mul]
  rw [ReciprocityTheory.L2DbarEstimates.wd_congr hE, ReciprocityTheory.L2DbarEstimates.wd, hG.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  push_cast
  linear_combination
    (-((fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) / 4) * I_sq

private theorem euclideanLeviForm_ofReal_eq_lemma_3 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.leviV n (fun y => (f y : ℂ)) x ξ =
      ∑ j, ∑ k, (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 *
          ξ j * conj (ξ k) := by
  simp only [ReciprocityTheory.L2DbarEstimates.leviV, wirtinger_wirtingerBar_ofReal_lemma_2 hf]

private theorem re_div_four_mul_mul_conj_mul_four (P Q : ℝ) (z w : ℂ) :
    (((P : ℂ) + I * (Q : ℂ)) / 4 * z * conj w).re * 4 =
      P * (z.re * w.re + z.im * w.im) - Q * (z.im * w.re - z.re * w.im) := by
  have h4 : ((P : ℂ) + I * (Q : ℂ)) / 4 = ((P / 4 : ℝ) : ℂ) + I * ((Q / 4 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h4]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem bilinear_apply_sum_sum (T : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℝ) (v w : Fin n → ReciprocityTheory.L2DbarEstimates.V n) :
    T (∑ j, v j) (∑ k, w k) = ∑ j, ∑ k, T (v j) (w k) := by
  have h : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, T (∑ j, v j) a = ∑ j, T (v j) a := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ContinuousLinearMap.sum_apply]
  rw [h]
  exact Finset.sum_congr rfl fun j _ => map_sum (T (v j)) w Finset.univ

theorem leviV_re_eq {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (f y : ℂ)) x ξ).re * 4 =
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k)))
          (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k))) +
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k))
          (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k)) := by
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hf, bilinear_apply_sum_sum, bilinear_apply_sum_sum]
  simp only [Complex.re_sum, Finset.sum_mul, re_div_four_mul_mul_conj_mul_four]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_add (f := _), map_sub, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem leviV_re_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (ξ : Fin n → ℂ) : (leviV n (fun y => (f y : ℂ)) x ξ).re ≤ 0 := by
  have h := leviV_re_eq hf ξ
  have h1 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • ReciprocityTheory.L2DbarEstimates.bas n k + (ξ k).im • (I • ReciprocityTheory.L2DbarEstimates.bas n k)))
  have h2 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • (I • ReciprocityTheory.L2DbarEstimates.bas n k) - (ξ k).im • ReciprocityTheory.L2DbarEstimates.bas n k))
  linarith

theorem leviV_ofReal_add {f g : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((f y + g y : ℝ) : ℂ)) x ξ =
      leviV n (fun y => (f y : ℂ)) x ξ + leviV n (fun y => (g y : ℂ)) x ξ := by
  have hfg : ContDiffAt ℝ 2 (fun y => f y + g y) x := hf.add hg
  have hT : fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x] fun y => fderiv ℝ f y + fderiv ℝ g y := by
      filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf,
        ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hg] with y hfy hgy
      exact fderiv_add hfy hgy
    rw [hev.fderiv_eq]
    exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_two' hf)
      (differentiableAt_fderiv_of_contDiffAt_two' hg)
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hfg, euclideanLeviForm_ofReal_eq_lemma_3 hf, euclideanLeviForm_ofReal_eq_lemma_3 hg, hT]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem leviV_ofReal_const_mul {f : V n → ℝ} {x : V n} (c : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y : ℝ) : ℂ)) x ξ = (c : ℂ) * leviV n (fun y => (f y : ℂ)) x ξ := by
  have hcf : ContDiffAt ℝ 2 (fun y => c * f y) x := contDiffAt_const.mul hf
  have hT : fderiv ℝ (fderiv ℝ (fun y => c * f y)) x = c • fderiv ℝ (fderiv ℝ f) x := by
    have hev : fderiv ℝ (fun y => c * f y) =ᶠ[𝓝 x] fun y => c • fderiv ℝ f y := by
      filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
      exact fderiv_const_mul hy c
    rw [hev.fderiv_eq]
    exact fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_two' hf) c
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hcf, euclideanLeviForm_ofReal_eq_lemma_3 hf, hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

open Finset

theorem mem_multiLe_iff {n j : ℕ} {α : Fin n → ℕ} : α ∈ multiLe n j ↔ ∑ i, α i ≤ j := by
  unfold multiLe
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hα⟩
    rw [Finset.mem_range] at ha
    rw [Nat.mem_antidiagonalTuple] at hα
    omega
  · intro h
    exact ⟨∑ i, α i, Finset.mem_range.2 (by omega), Nat.mem_antidiagonalTuple.2 rfl⟩

theorem card_multiLe_succ (n j : ℕ) :
    (multiLe (n + 1) j).card = ∑ a ∈ range (j + 1), (multiLe n (j - a)).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij' (fun α _ => (⟨α 0, Fin.tail α⟩ : Σ _ : ℕ, Fin n → ℕ))
    (fun p _ => (Fin.cons p.1 p.2 : Fin (n + 1) → ℕ)) ?_ ?_ ?_ ?_
  · intro α hα
    simp only [mem_multiLe_iff, Fin.sum_univ_succ] at hα
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff, Fin.tail]
    exact ⟨by omega, by omega⟩
  · rintro ⟨a, β⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff] at hp
    simp only [mem_multiLe_iff, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  · intro α _
    exact Fin.cons_self_tail α
  · rintro ⟨a, β⟩ _
    simp only [Fin.cons_zero, Fin.tail_cons]

theorem ind_count : INDCountStatement := by
  unfold INDCountStatement
  intro n
  induction n with
  | zero =>
    intro j
    have h : multiLe 0 j = {finZeroElim} := by
      ext α
      simp only [mem_multiLe_iff, Finset.mem_singleton, Fin.sum_univ_zero]
      exact ⟨fun _ => funext fun i => i.elim0, fun _ => Nat.zero_le _⟩
    rw [h, Finset.card_singleton]
    simp
  | succ n ih =>
    intro j
    induction j with
    | zero =>
      rw [card_multiLe_succ, Finset.sum_range_one, ih]
      simp
    | succ j ihj =>
      rw [card_multiLe_succ, Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      rw [← card_multiLe_succ n j, ihj, ih (j + 1)]
      have h1 : (j + (n + 1)).choose (n + 1) = (j + 1 + n).choose (n + 1) := by
        congr 1
        omega
      have h2 : (j + 1 + (n + 1)).choose (n + 1) =
          (j + 1 + n).choose n + (j + 1 + n).choose (n + 1) := by
        rw [show j + 1 + (n + 1) = (j + 1 + n) + 1 by omega]
        exact Nat.choose_succ_succ' _ _
      omega

end

end ReciprocityTheory.L2DbarEstimates.Y
end

