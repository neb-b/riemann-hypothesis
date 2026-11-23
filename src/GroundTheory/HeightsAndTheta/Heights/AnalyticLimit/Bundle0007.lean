module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0005
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PChartCont
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

theorem continuousOn_of_chart_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {U : Set X} (hU : IsOpen U) {E : Type} [TopologicalSpace E] (h : X → E)
    (hc : ∀ j, ContinuousOn (h ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn h U := by
  intro x hx
  obtain ⟨m, hm⟩ := A.cover x
  set c := A.chart m
  have hT : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hcx : c x ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hm, by simpa [c.left_inv hm] using hx⟩
  have h1 : ContinuousAt (h ∘ c.symm) (c x) := (hc m).continuousAt (hT.mem_nhds hcx)
  have h2 : ContinuousAt ((h ∘ c.symm) ∘ c) x := by
    apply ContinuousAt.comp (f := c)
    · exact h1
    · exact c.continuousAt hm
  have heq : (h ∘ c.symm) ∘ c =ᶠ[nhds x] h := by
    filter_upwards [c.open_source.mem_nhds hm] with y hy
    simp [c.left_inv hy]
  exact (h2.congr heq).continuousWithinAt

theorem ChartCont.proof : ChartCont.Statement := by
  intro X _ D A U hU
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · exact continuousOn_of_chart_continuousOn A hU f fun j => (hf j).continuousOn
  · exact continuousOn_of_chart_continuousOn A hU g fun j => (hg j).continuousOn

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PCoordDivDivisible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem cofactor_vanish {D : ℕ} {Ω : Set (Fin D → ℂ)} (hΩ : IsOpen Ω) {F G : (Fin D → ℂ) → ℂ}
    {i k : Fin D} (hik : k ≠ i) (hG : AnalyticOnNhd ℂ G Ω) (hFG : ∀ z ∈ Ω, F z = z i * G z)
    (hF : ∀ z ∈ Ω, z k = 0 → F z = 0) {z : Fin D → ℂ} (hz : z ∈ Ω) (hzk : z k = 0) : G z = 0 := by
  classical
  by_cases hzi : z i = 0
  swap
  · have h := hFG z hz
    rw [hF z hz hzk] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hzi

  set w : ℂ → (Fin D → ℂ) := fun ε => Function.update z i ε with hw
  have hwc : Continuous w := continuous_const.update i continuous_id
  have hw0 : w 0 = z := by rw [← hzi]; simp [hw]
  have hcont : ContinuousAt (fun ε => G (w ε)) 0 := by
    have h := (hG z hz).continuousAt
    rw [← hw0] at h
    exact h.comp hwc.continuousAt
  have hmem : ∀ᶠ ε in 𝓝 (0 : ℂ), w ε ∈ Ω := by
    exact hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact hΩ.mem_nhds hz)

  have hzero : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), G (w ε) = 0 := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with ε hε hne
    have hwk : w ε k = 0 := by simp [hw, hik, hzk]
    have hwi : w ε i = ε := by simp [hw]
    have h := hFG _ hε
    rw [hF _ hε hwk, hwi] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  have ht1 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (G (w 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)
  have h := tendsto_nhds_unique ht1 ht2
  rwa [hw0] at h

theorem CoordDivDivisible.proof (hH : HyperplaneDivisible.Statement) : CoordDivDivisible.Statement := by
  classical
  intro D Ω F S hΩ hFa hF
  induction S using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hFa, fun z _ => by simp⟩
  | insert i S hi ih =>
    obtain ⟨G₁, hG₁a, hG₁⟩ := hH D Ω F i hΩ hFa fun z hz hzi =>
      hF z hz ⟨i, Finset.mem_insert_self i S, hzi⟩
    have hG₁0 : ∀ z ∈ Ω, z ∈ coordDiv S → G₁ z = 0 := by
      rintro z hz ⟨k, hk, hzk⟩
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      exact cofactor_vanish hΩ hki hG₁a hG₁
        (fun y hy hyk => hF y hy ⟨k, Finset.mem_insert_of_mem hk, hyk⟩) hz hzk
    obtain ⟨G, hGa, hG⟩ := ih G₁ hG₁a hG₁0
    refine ⟨G, hGa, fun z hz => ?_⟩
    rw [hG₁ z hz, hG z hz, Finset.prod_insert hi, mul_assoc]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PHyperplaneDivisible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric Set Filter Topology
open scoped Interval

noncomputable section

def coordScale {D : ℕ} (i : Fin D) (t : ℝ) : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) :=
  ContinuousLinearMap.id ℂ _ +
    ((t : ℂ) - 1) • (ContinuousLinearMap.proj i : (Fin D → ℂ) →L[ℂ] ℂ).smulRight (Pi.single i (1 : ℂ))

variable {D : ℕ}

theorem coordScale_apply (i : Fin D) (t : ℝ) (v : Fin D → ℂ) (j : Fin D) :
    coordScale i t v j = if j = i then (t : ℂ) * v i else v j := by
  simp only [coordScale]
  simp only [Pi.single_apply, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  split_ifs <;> subst_vars <;> ring

theorem coordScale_of_eq_zero (i : Fin D) (t : ℝ) {v : Fin D → ℂ} (hv : v i = 0) : coordScale i t v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp [hv]
  · rfl

theorem coordScale_one (i : Fin D) (v : Fin D → ℂ) : coordScale i 1 v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp
  · rfl

theorem norm_coordScale_apply_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : Fin D → ℂ) :
    ‖coordScale i t v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => ?_
  rw [coordScale_apply]
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_le_pi_norm v i)
  · exact norm_le_pi_norm v j

theorem norm_coordScale_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖coordScale i t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using norm_coordScale_apply_le i ht v

theorem coordScale_mem_ball (i : Fin D) {p z : Fin D → ℂ} {r t : ℝ} (hp : p i = 0) (hz : z ∈ ball p r)
    (ht : t ∈ Icc (0 : ℝ) 1) : coordScale i t z ∈ ball p r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  calc ‖coordScale i t z - p‖ = ‖coordScale i t (z - p)‖ := by
        rw [map_sub, coordScale_of_eq_zero i t hp]
    _ ≤ ‖z - p‖ := norm_coordScale_apply_le i ht _
    _ < r := hz

theorem hasDerivAt_coordScale (i : Fin D) (z : Fin D → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordScale i s z) (z i • Pi.single i (1 : ℂ)) t := by
  have h := (((hasDerivAt_id t).ofReal_comp.sub_const (1 : ℂ)).smul_const
    (z i • Pi.single i (1 : ℂ) : Fin D → ℂ)).const_add z
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  funext j
  show coordScale i s z j = _
  rw [coordScale_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, id_eq]
  split_ifs <;> subst_vars <;> ring

theorem continuous_coordScale (i : Fin D) : Continuous (coordScale (D := D) i) :=
  continuous_const.add (((Complex.continuous_ofReal).sub continuous_const).smul continuous_const)

theorem analyticOnNhd_fderiv_apply {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    (v : Fin D → ℂ) : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w v) Ω := fun w hw =>
  (((ContinuousLinearMap.apply ℂ ℂ (E' := Fin D → ℂ) v).analyticAt (fderiv ℂ F w)).comp
    (hF.fderiv w hw)).congr (Eventually.of_forall fun _ => rfl)

theorem eq_mul_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) (h0 : ∀ z ∈ Ω, z i = 0 → F z = 0) {p : Fin D → ℂ} {r : ℝ}
    (hp : p i = 0) (hball : ball p r ⊆ Ω) {z : Fin D → ℂ} (hz : z ∈ ball p r) :
    F z = z i * ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1) := by
  have hFi : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w (Pi.single i 1)) Ω := analyticOnNhd_fderiv_apply hF _
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t z ∈ Ω := fun t ht => hball (coordScale_mem_ball i hp hz ht)
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (coordScale i s z))
      (z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 := ((hF _ (hmem t ht)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (hasDerivAt_coordScale i z t)
    refine h1.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : ContinuousOn (fun t : ℝ => z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) (uIcc 0 1) := by
    refine continuousOn_const.mul (hFi.continuousOn.comp
      ((continuous_coordScale i).clm_apply continuous_const).continuousOn fun t ht => hmem t ?_)
    rwa [uIcc_of_le zero_le_one] at ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, coordScale_one,
    h0 _ (hmem 0 ⟨le_rfl, zero_le_one⟩) (by simp [coordScale_apply])] at h
  rw [h, sub_zero]

theorem differentiableOn_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) {p : Fin D → ℂ} {r : ℝ} (hp : p i = 0) (hball : ball p r ⊆ Ω) (hr : 0 < r) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1))
      (ball p (r / 2)) := by
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  have hFi : AnalyticOnNhd ℂ Fi Ω := analyticOnNhd_fderiv_apply hF _
  have hK : closedBall p (r / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hB : ball p (r / 2) ⊆ Ω := ball_subset_closedBall.trans hK
  obtain ⟨C, hC⟩ := (isCompact_closedBall p (r / 2)).exists_bound_of_continuousOn
    (hFi.fderiv.continuousOn.mono hK)
  have hI : ∀ {t : ℝ}, t ∈ Ι (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 := fun ht =>
    Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
  have hmem : ∀ x ∈ ball p (r / 2), ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t x ∈ ball p (r / 2) :=
    fun x hx t ht => coordScale_mem_ball i hp hx ht
  have hcont : ∀ x ∈ ball p (r / 2), ContinuousOn (fun t : ℝ => Fi (coordScale i t x)) (Icc 0 1) :=
    fun x hx => hFi.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x hx t ht)
  intro x₀ hx₀
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (F' := fun x t => (fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)) (bound := fun _ => C)
    (isOpen_ball.mem_nhds hx₀) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
    exact ((hcont x hx).mono fun t ht => hI ht).aestronglyMeasurable measurableSet_uIoc
  · exact (hcont x₀ hx₀).intervalIntegrable_of_Icc zero_le_one
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact ((hFi.fderiv.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x₀ hx₀ t (hI ht))).clm_comp (continuous_coordScale i).continuousOn)
  · refine Eventually.of_forall fun t ht x hx => ?_
    calc ‖(fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)‖
        ≤ ‖fderiv ℂ Fi (coordScale i t x)‖ * ‖coordScale i t‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul (hC _ (ball_subset_closedBall (hmem x hx t (hI ht))))
          (norm_coordScale_le i (hI ht)) (norm_nonneg _)
          ((norm_nonneg _).trans (hC p (mem_closedBall_self (half_pos hr).le)))
      _ = C := mul_one C
  · refine Eventually.of_forall fun t ht x hx => ?_
    exact (hFi _ (hB (hmem x hx t (hI ht)))).differentiableAt.hasFDerivAt.comp x (coordScale i t).hasFDerivAt

theorem HyperplaneDivisible.proof : HyperplaneDivisible.Statement := by
  intro D Ω F i hΩ hF h0
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  refine ⟨fun z => if z i = 0 then Fi z else F z / z i, fun p hp => ?_, fun z hz => ?_⟩
  · by_cases hpi : p i = 0
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
      have hH := ReciprocityTheory.AnForm.Osgood.osgood D _ _ isOpen_ball
        (differentiableOn_integral_partial hF hpi hball hr) p (mem_ball_self (half_pos hr))
      refine hH.congr ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (half_pos hr))] with z hz
      have hz' : z ∈ ball p r := ball_subset_ball (half_le_self hr.le) hz
      by_cases hzi : z i = 0
      · simp only [if_pos hzi, coordScale_of_eq_zero i _ hzi, intervalIntegral.integral_const, Fi]
        simp
      · rw [if_neg hzi, eq_mul_integral_partial hF h0 hpi hball hz', mul_div_cancel_left₀ _ hzi]
    · have hproj : AnalyticAt ℂ (fun z : Fin D → ℂ => z i) p :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt p
      refine ((hF p hp).div hproj hpi).congr ?_
      filter_upwards [(isOpen_ne_fun (continuous_apply i) continuous_const).mem_nhds hpi] with z hz
      simp only [if_neg (show z i ≠ 0 from hz)]
      rfl
  · by_cases hzi : z i = 0
    · simp [hzi, h0 z hz hzi]
    · simp only [if_neg hzi]
      rw [mul_div_cancel₀ _ hzi]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PIndicatorSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open Filter Topology
open scoped ContDiff

theorem IndicatorSmooth.proof : IndicatorSmooth.Statement := by
  intro X _ D A U O χ h hU hO hχ hsupp hh j
  set φ := A.chart j
  refine fun v hv => (?_ : ContDiffAt ℝ ∞ _ v).contDiffWithinAt
  by_cases hx : φ.symm v ∈ O
  ·
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := φ.isOpen_inter_preimage_symm (hU.inter hO)
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ O) := ⟨hv.1, hv.2, hx⟩
    have hχT : ContDiffOn ℝ ∞ (χ ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) :=
      (hχ j).mono fun z hz => ⟨hz.1, Set.mem_univ _⟩
    have hprod : ContDiffOn ℝ ∞ (fun z => (χ ∘ φ.symm) z * (h ∘ φ.symm) z)
        (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := hχT.mul (hh j)
    refine (hprod.contDiffAt (hT.mem_nhds hvT)).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    simp [Function.comp, Set.indicator_of_mem hz.2.2]
  ·
    have hns : φ.symm v ∉ tsupport χ := fun hm => hx (hsupp hm)
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ) :=
      φ.isOpen_inter_preimage_symm (isClosed_tsupport χ).isOpen_compl
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ := ⟨hv.1, hns⟩
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    have h0 : χ (φ.symm z) = 0 := image_eq_zero_of_notMem_tsupport hz.2
    by_cases hzO : φ.symm z ∈ O
    · simp [Function.comp, Set.indicator_of_mem hzO, h0]
    · simp [Function.comp, Set.indicator_of_notMem hzO]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem continuousOn_of_holoOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) : ContinuousOn g W := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]; exact hx⟩
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  have heq : (g ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[nhds x] g := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [Function.comp, (A.chart j).left_inv hz]
  exact (h2.congr heq).continuousWithinAt

theorem logNormHolo_of_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hW : IsOpen W) (hg : A.HoloOn W g) (hgc : ContinuousOn g W)
    (hne : ∀ y ∈ W, g y ≠ 0) {y : X} (hy : y ∈ W) : ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re := by
  have hc : g y ≠ 0 := hne y hy
  have hcn : 0 < ‖g y‖ := norm_pos_iff.2 hc

  have hslit : ∀ w ∈ Metric.ball (g y) ‖g y‖, w / g y ∈ Complex.slitPlane := by
    intro w hw
    apply Complex.ball_one_subset_slitPlane
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : w / g y - 1 = (w - g y) / g y := by field_simp
    rw [this, norm_div, div_lt_one hcn]
    exact hw
  refine ⟨W ∩ g ⁻¹' Metric.ball (g y) ‖g y‖, hgc.isOpen_inter_preimage hW Metric.isOpen_ball,
    ⟨hy, by simpa using hcn⟩, Set.inter_subset_left,
    fun z => Complex.log (g z / g y) + (Real.log ‖g y‖ : ℂ), ?_, ?_⟩
  · intro j v hv
    have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hg j v ⟨hv.1, hv.2.1⟩
    have hs : (g ∘ (A.chart j).symm) v / g y ∈ Complex.slitPlane := hslit _ hv.2.2
    exact ((ha.div analyticAt_const hc).clog hs).add analyticAt_const
  · intro z hz
    have hz0 : g z ≠ 0 := hne z hz.1
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 hc)]
    ring

theorem LogNormHolo.proof (hCC : ChartCont.Statement) : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg ((hCC D A W hW).2 g hg) hne hy

theorem LogNormHolo.full : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg (continuousOn_of_holoOn A hg) hne hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PNormSqSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open scoped ContDiff

theorem NormSqSmooth.proof : NormSqSmooth.Statement := by
  intro X _ D A U g hg j
  have h1 : ContDiffOn ℝ ∞ (g ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    ((hg j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact h2.comp_contDiffOn h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegRCont
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem RegRCont.proof : RegRCont.Statement := by
  intro X _ D A R y hy
  set j := bdIdx R y
  have hyU : y ∈ bdDom R j := mem_bdDom_bdIdx R y
  let g : (Fin D → ℂ) → ℝ := fun z =>
    Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have key : ∀ y' ∈ bdDom R j ∩ R.Yo,
      R.ψ j y' ∉ coordDiv (R.S j) ∧ R.r y' = g (R.ψ j y') := by
    rintro y' ⟨⟨hs, hW⟩, hY⟩
    have hinv : (R.ψ j).symm (R.ψ j y') = y' := (R.ψ j).left_inv hs
    have hnot : R.ψ j y' ∉ coordDiv (R.S j) :=
      (R.mem_Yo_iff j _ hW).1 (by rw [hinv]; exact hY)
    refine ⟨hnot, ?_⟩
    have h := R.r_chart j (R.ψ j y') ⟨hW, hnot⟩
    rw [hinv] at h
    exact h
  have hg : ContinuousAt g (R.ψ j y) := by
    have hW : R.ψ j y ∈ R.W j := hyU.2
    have hnd := (key y ⟨hyU, hy⟩).1
    have hf : ContinuousAt (R.f j) (R.ψ j y) :=
      (R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW)
    refine (continuousAt_const.add hf).sub ?_
    refine tendsto_finsetSum (R.S j) fun i hi => ?_
    have hzi : R.ψ j y i ≠ 0 := fun h0 => hnd ⟨i, hi, h0⟩
    have hc : ContinuousAt (fun z : Fin D → ℂ => ‖z i‖ ^ 2) (R.ψ j y) :=
      ((continuous_apply i).norm.pow 2).continuousAt
    exact hc.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hzi))
  have hO : IsOpen (bdDom R j ∩ R.Yo) := (isOpen_bdDom R j).inter R.isOpen_Yo
  have heq : g ∘ R.ψ j =ᶠ[𝓝 y] R.r :=
    Filter.eventually_of_mem (hO.mem_nhds ⟨hyU, hy⟩) fun y' h => ((key y' h).2).symm
  exact ((hg.comp ((R.ψ j).continuousAt hyU.1)).congr heq).continuousWithinAt

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegYoDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)

theorem dense_compl_coordDiv {D : ℕ} (S : Finset (Fin D)) : Dense (coordDiv S)ᶜ := by
  have h : (coordDiv S)ᶜ = ⋂ i ∈ (S : Set (Fin D)), (fun z : Fin D → ℂ => z i) ⁻¹' ({0}ᶜ) := by
    ext z
    simp [coordDiv]
  rw [h]
  refine dense_biInter_of_isOpen (fun i _ => ?_) S.countable_toSet (fun i _ => ?_)
  · exact isOpen_compl_singleton.preimage (continuous_apply i)
  · exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)

theorem RegYoDense.proof : RegYoDense.Statement := by
  intro X _ D A R
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hxU⟩
  have hxj : x ∈ bdDom R (bdIdx R x) := mem_bdDom_bdIdx R x
  set j := bdIdx R x
  have hO : IsOpen ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))) :=
    (R.ψ j).isOpen_image_source_inter (hU.inter (isOpen_bdDom R j))
  have hne : ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))).Nonempty :=
    ⟨R.ψ j x, x, ⟨hxj.1, hxU, hxj⟩, rfl⟩
  obtain ⟨z, ⟨y, ⟨hys, hyU, hyD⟩, rfl⟩, hz⟩ :=
    (dense_compl_coordDiv (R.S j)).inter_open_nonempty _ hO hne
  have hYo := (R.mem_Yo_iff j (R.ψ j y) hyD.2).2 hz
  rw [(R.ψ j).left_inv hys] at hYo
  exact ⟨y, hyU, hYo⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

