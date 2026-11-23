module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier tmax regMax le_tmax tmax_le regMax_ge regMax_le)

noncomputable section

namespace LogLogRegularisation

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}


open Classical in
theorem le_glue (P : PotentialCharts A) (a : Fin P.N → X → ℝ) {ε : ℝ} (hε : 0 ≤ ε) {x : X}
    {j : Fin P.N} (hx : x ∈ P.mid j) : a j x ≤ P.glue a ε x := by
  unfold PotentialCharts.glue
  exact le_add_of_le_of_nonneg
    ((le_tmax (fun i : {i // x ∈ P.mid i} => a i x) ⟨j, hx⟩).trans (regMax_ge ε _)) (by linarith)


open Classical in
theorem glue_le (P : PotentialCharts A) (a : Fin P.N → X → ℝ) {ε c : ℝ} (hε : 0 ≤ ε) {x : X}
    (h : ∀ j, x ∈ P.mid j → a j x ≤ c) : P.glue a ε x ≤ c + ε := by
  unfold PotentialCharts.glue
  have h1 := regMax_le hε (fun i : {i // x ∈ P.mid i} => a i x)
  have h2 : tmax (fun i : {i // x ∈ P.mid i} => a i x) ≤ c := tmax_le fun i => h i.1 i.2
  linarith

end LogLogRegularisation

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

section ChangeOfChart

variable {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}

theorem comp_symm_eventuallyEq {E : Type*} (g : X → E) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) :
    (g ∘ (A.chart i).symm) ∘ (A.chart i ∘ ψ.symm) =ᶠ[𝓝 (ψ x)] g ∘ ψ.symm := by
  have h : ∀ᶠ y in 𝓝 (ψ x), ψ.symm y ∈ (A.chart i).source :=
    (ψ.continuousAt_symm (ψ.map_source hx)).preimage_mem_nhds
      (by rw [ψ.left_inv hx]; exact (A.chart i).open_source.mem_nhds hxi)
  filter_upwards [h] with y hy
  simp [(A.chart i).left_inv hy]

theorem analyticAt_chart_comp_symm (hψ : IsCompatChart A ψ) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (ψ x) :=
  (hψ i).2 (ψ x) ⟨ψ.map_source hx, by simp [ψ.left_inv hx, hxi]⟩

theorem analyticAt_comp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hψ : IsCompatChart A ψ) {g : X → E} {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) (hg : AnalyticAt ℂ (g ∘ (A.chart i).symm) (A.chart i x)) :
    AnalyticAt ℂ (g ∘ ψ.symm) (ψ x) := by
  have hτ := analyticAt_chart_comp_symm hψ hx i hxi
  have hg' : AnalyticAt ℂ (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x)) := by
    simpa [ψ.left_inv hx] using hg
  exact (hg'.comp hτ).congr (comp_symm_eventuallyEq g hx i hxi)

theorem contDiffAt_comp_symm (hψ : IsCompatChart A ψ) {n : WithTop ℕ∞} {g : X → ℝ} {x : X}
    (hx : x ∈ ψ.source) (i : Fin A.n) (hxi : x ∈ (A.chart i).source)
    (hg : ContDiffAt ℝ n (g ∘ (A.chart i).symm) (A.chart i x)) :
    ContDiffAt ℝ n (g ∘ ψ.symm) (ψ x) := by
  have hτ := (analyticAt_chart_comp_symm hψ hx i hxi).restrictScalars (𝕜 := ℝ)
  have hg' : ContDiffAt ℝ n (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x)) := by
    simpa [ψ.left_inv hx] using hg
  exact (hg'.comp (ψ x) hτ.contDiffAt).congr_of_eventuallyEq
    (comp_symm_eventuallyEq g hx i hxi).symm

theorem analyticAt_transition {ψ' : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ)
    (hψ' : IsCompatChart A ψ') {x : X} (hx : x ∈ ψ.source) (hx' : x ∈ ψ'.source) :
    AnalyticAt ℂ (ψ' ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  refine analyticAt_comp_symm hψ hx i hi ((hψ' i).1 (A.chart i x) ⟨(A.chart i).map_source hi, ?_⟩)
  simp [(A.chart i).left_inv hi, hx']

theorem contDiffAt_comp_symm_of_smoothOn (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : A.SmoothOn U f) {x : X} (hxU : x ∈ U) (hx : x ∈ ψ.source) :
    ContDiffAt ℝ ∞ (f ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  exact contDiffAt_comp_symm hψ hx i hi (smoothOn_contDiffAt hU hf hi hxU)
where

  smoothOn_contDiffAt {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) {i : Fin A.n}
      {x : X} (hi : x ∈ (A.chart i).source) (hxU : x ∈ U) :
      ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) :=
    (hf i).contDiffAt (((A.chart i).continuousOn_symm.isOpen_inter_preimage
      (A.chart i).open_target hU).mem_nhds ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxU]⟩)

theorem analyticAt_comp_symm_of_holoOn (hψ : IsCompatChart A ψ) {W : Set X}
    {G : X → ℂ} (hG : A.HoloOn W G) {x : X} (hxW : x ∈ W) (hx : x ∈ ψ.source) :
    AnalyticAt ℂ (G ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  exact analyticAt_comp_symm hψ hx i hi
    (hG i (A.chart i x) ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxW]⟩)

end ChangeOfChart

theorem isPsh_congr {U : Set (Fin D → ℂ)} {φ ψ : (Fin D → ℂ) → ℝ} (h : EqOn φ ψ U)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[U] z, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h hxU]
  · have hs : EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ => ψ (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
      fun ζ hζ => h (hd ζ (by simp at hζ; rw [hζ]))
    obtain ⟨h1, h2⟩ := hφ.2 z w hd
    refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    rw [← Real.circleAverage_congr_sphere hs, ← h hz]
    exact h2

namespace RegChartData

variable (R : RegChartData A)

theorem isOpen_Yo : IsOpen R.Yo := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨j, hj⟩ := R.cover x
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  have hV : IsOpen ((R.chart j).source ∩ R.chart j ⁻¹' (coordDiv (R.S j))ᶜ) :=
    (R.chart j).continuousOn.isOpen_inter_preimage (R.chart j).open_source
      (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _).isOpen_compl
  refine Filter.mem_of_superset (hV.mem_nhds ⟨hxs, (R.mem_Yo j x hxs).1 hx⟩) fun y hy => ?_
  exact (R.mem_Yo j y hy.1).2 hy.2

theorem symm_mem_Yo (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : (R.chart j).symm y ∈ R.Yo :=
  (R.mem_Yo j _ ((R.chart j).map_target hy)).2 (by rwa [(R.chart j).right_inv hy])

theorem continuousOn_u (j : Fin R.N) :
    ContinuousOn (R.u j) ((R.chart j).target \ coordDiv (R.S j)) := by
  intro y hy
  have hq : ContinuousAt (R.q j) y :=
    ((R.q_smooth j).continuousOn).continuousAt ((R.chart j).open_target.mem_nhds hy.1)
  have hx : (R.chart j).symm y ∈ (R.chart j).source := (R.chart j).map_target hy.1
  have hph := contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo R.ph_smooth
    (R.symm_mem_Yo j hy.1 hy.2) hx
  rw [(R.chart j).right_inv hy.1] at hph
  exact (hq.add hph.continuousAt).continuousWithinAt

theorem smoothed_local (ρ : Mollifier D) (K : ℝ) {t : ℝ} (ht : 0 < t) (j : Fin R.N)
    {z : Fin D → ℂ} (hz : closedBall z t ⊆ (R.chart j).target) :
    ContDiffAt ℝ ∞ (R.smoothed ρ K t j) z ∧ ∀ w, 0 ≤ levi (R.smoothed ρ K t j) z w := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall z t).exists_cthickening_subset_open (R.chart j).open_target hz
  rw [cthickening_closedBall hδ.le ht.le] at hδsub
  set U' := ball z (δ + t) with hU'
  have hU'sub : U' ⊆ (R.chart j).target := ball_subset_closedBall.trans hδsub
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (δ + t)).bddAbove_image
    ((R.q_smooth j).continuousOn.mono hδsub)

  have hcont : ContinuousOn (R.u j) (U' \ coordDiv (R.S j)) :=
    (R.continuousOn_u j).mono (sdiff_subset_sdiff_left hU'sub)
  have hpsh : IsPsh (U' \ coordDiv (R.S j)) (R.u j) :=
    isPsh_mono (R.u_psh j) (sdiff_subset_sdiff_left hU'sub)
  have hbound : ∀ y ∈ U' \ coordDiv (R.S j), R.u j y ≤
      |M + R.Cph| * Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
    intro y hy
    have hyt : y ∈ (R.chart j).target := hU'sub hy.1
    have h1 : R.q j y ≤ M := hM ⟨y, ball_subset_closedBall hy.1, rfl⟩
    have h2 : R.ph ((R.chart j).symm y) ≤ R.Cph := R.ph_le _ (R.symm_mem_Yo j hyt hy.2)
    have hy1 : ‖y‖ < 1 := by simpa using R.target_subset j hyt
    have hs : 0 ≤ ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
      rw [Real.log_inv]
      exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
    have hL : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
      have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
      rwa [Real.log_exp] at this
    have : R.u j y = R.q j y + R.ph ((R.chart j).symm y) := rfl
    calc R.u j y ≤ M + R.Cph := by rw [this]; linarith
      _ ≤ |M + R.Cph| := le_abs_self _
      _ ≤ _ := le_mul_of_one_le_right (abs_nonneg _) hL
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm D (R.S j) U' (R.u j) |M + R.Cph| isOpen_ball
    (hU'sub.trans (R.target_subset j)) hcont hpsh hbound).2 K

  have heq : EqOn (limsupExt U' (coordDiv (R.S j)) (fun y => max (R.u j y) (-K)))
      (R.trunc K j) U' := by
    intro y hy
    simp only [RegChartData.trunc, limsupExt]
    split_ifs with hA
    · congr 1
      rw [nhdsWithin_restrict ((R.chart j).target \ coordDiv (R.S j)) hy isOpen_ball]
      congr 1
      ext v
      constructor
      · rintro ⟨hv1, hv2⟩; exact ⟨⟨hU'sub hv1, hv2⟩, hv1⟩
      · rintro ⟨⟨-, hv2⟩, hv1⟩; exact ⟨hv1, hv2⟩
    · rfl
  have htr : IsPsh U' (R.trunc K j) := isPsh_congr heq hext
  obtain ⟨hopen, hsm, hpm, -⟩ := (ReciprocityTheory.AnForm.A.mollify_thm D ρ U' (R.trunc K j) isOpen_ball htr).1 t ht
  have hz' : z ∈ shrink U' t := closedBall_subset_ball (lt_add_of_pos_left t hδ)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D (shrink U' t) _ hopen
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1 hpm
  exact ⟨hsm.contDiffAt (hopen.mem_nhds hz'), fun w => hlevi.2 z hz' w⟩

end RegChartData

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.IsCompactImageClosureMid
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)

noncomputable section

theorem continuous_of_atlasSmooth {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    simpa using (hf j).continuousOn
  have h2 := (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
    ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem regMax_bounds {ι : Type} [Fintype ι] [Nonempty ι] {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    tmax t ≤ regMax η t ∧ regMax η t ≤ tmax t + η / 2 := by
  classical
  exact ((ReciprocityTheory.AnForm.A.regMax_thm ι).1 η hη).2.2.2.1 t

namespace PotentialCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

theorem isCompact_image_closure_mid [CompactSpace X] (j : Fin P.N) :
    IsCompact ((P.chart j) '' closure (P.mid j)) :=
  isClosed_closure.isCompact.image_of_continuousOn
    ((P.chart j).continuousOn.mono (P.closure_mid j))

theorem exists_margin [CompactSpace X] :
    ∃ δ > 0, ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target := by
  have h : ∀ j, ∃ δ, 0 < δ ∧
      cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target :=
    fun j => (P.isCompact_image_closure_mid j).exists_cthickening_subset_open
      (P.chart j).open_target
      (image_subset_iff.2 fun x hx => (P.chart j).map_source (P.closure_mid j hx))
  choose δ hδ hsub using h
  by_cases hN : Nonempty (Fin P.N)
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_min δ
    exact ⟨δ j₀, hδ j₀, fun j => (cthickening_mono (hj₀ j) _).trans (hsub j)⟩
  · exact ⟨1, one_pos, fun j => (hN ⟨j⟩).elim⟩

theorem exists_bound_q [CompactSpace X] {δ : ℝ}
    (hδ : ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target) :
    ∃ Q : ℝ, ∀ j, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), |P.q j y| ≤ Q := by
  have h : ∀ j, ∃ Q : ℝ, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), ‖P.q j y‖ ≤ Q :=
    fun j => (P.isCompact_image_closure_mid j).cthickening.exists_bound_of_continuousOn
      ((P.q_smooth j).continuousOn.mono (hδ j))
  choose Q hQ using h
  refine ⟨∑ j, |Q j|, fun j y hy => ?_⟩
  calc |P.q j y| = ‖P.q j y‖ := (Real.norm_eq_abs _).symm
    _ ≤ Q j := hQ j y hy
    _ ≤ |Q j| := le_abs_self _
    _ ≤ ∑ j, |Q j| := Finset.single_le_sum (fun i _ => abs_nonneg (Q i)) (Finset.mem_univ j)

end PotentialCharts

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartMollifiedBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)

noncomputable section

theorem trunc_ge_of_bdd {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (K B : ℝ) (j : Fin R.N) {V : Set (Fin D → ℂ)} (hVo : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) (hb : ∀ y ∈ V, R.trunc K j y ≤ B) {y : Fin D → ℂ} (hy : y ∈ V) :
    -K ≤ R.trunc K j y := by
  unfold RegChartData.trunc limsupExt
  split_ifs with hA
  · have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S j) (R.chart j).open_target (hVt hy)
    have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[(R.chart j).target \ coordDiv (R.S j)] y)
        (fun y => max (R.u j y) (-K)) := by
      refine isBoundedUnder_of_eventually_le (a := B) ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy), self_mem_nhdsWithin]
        with y' hy'V hy'
      have h := hb y' hy'V
      simp only [RegChartData.trunc, limsupExt, if_neg hy'.2] at h
      exact h
    refine le_limsup_of_le hbdd (fun b hb' => ?_)
    obtain ⟨y', hy'⟩ := hb'.exists
    exact (le_max_right _ _).trans hy'
  · exact le_max_right (R.u j y) (-K)

theorem le_molli_of_ge {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, c ≤ φ y) : c ≤ molli ρ t φ z := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc c = ∫ y, ρ.scaled t y * c := by
        rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]
    _ ≤ _ := by
      refine integral_mono ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _)
        (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z) fun y => ?_
      by_cases hy : ρ.scaled t y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
      have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
      rw [indicator_of_mem hmem]
      exact hc _ hmem

theorem ChartMollifiedBounds.proof (h : TruncPsh.Statement) : ChartMollifiedBounds.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B, hδ, hV⟩ := h X D A R
  choose V hVo hVt hVball hVpsh using hV

  have hcpt : ∀ j, IsCompact (R.chart j '' closure (R.mid j)) := fun j =>
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have himg : ∀ j, R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := by
    rintro j _ ⟨x, hx, rfl⟩
    exact (R.chart j).map_source (R.closure_mid j hx)
  choose r hr hrt using fun j => (hcpt j).exists_cthickening_subset_open (R.chart j).open_target (himg j)

  obtain ⟨ε, hε, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ j, ε ≤ r j := by
    rcases isEmpty_or_nonempty (Fin R.N) with hN | hN
    · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.univ.exists_min_image r Finset.univ_nonempty
      exact ⟨r j₀, hr j₀, fun j => hj₀ j (Finset.mem_univ j)⟩

  choose Cq hCq using fun j => (hcpt j).exists_bound_of_continuousOn
    (((R.q_smooth j).continuousOn).mono (himg j))
  refine ⟨max B 0 + ∑ j, |Cq j|, min δ ε, lt_min hδ hε, fun t ht ht₀ => ⟨?_, ?_⟩⟩
  · intro j x hx
    exact (closedBall_subset_cthickening (mem_image_of_mem _ hx) t).trans
      ((cthickening_mono ((ht₀.trans_le (min_le_right _ _)).le.trans (hεr j)) _).trans (hrt j))
  intro K hK j x hx
  have hxs : x ∈ (R.chart j).source := R.closure_mid j (subset_closure hx)
  obtain ⟨hpsh, hbd⟩ := hVpsh j K
  have htδ : t ≤ δ := (ht₀.trans_le (min_le_left _ _)).le
  have hball : closedBall (R.chart j x) t ⊆ V j :=
    (closedBall_subset_closedBall htδ).trans (hVball j x hx)
  have hq : |R.q j (R.chart j x)| ≤ ∑ j, |Cq j| := by
    have h1 := hCq j (R.chart j x) (mem_image_of_mem _ (subset_closure hx))
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Cq j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))

  have hlow : -K ≤ molli ρ t (R.trunc K j) (R.chart j x) :=
    le_molli_of_ge ρ (hVo j) hpsh ht hball fun y hy =>
      trunc_ge_of_bdd R K _ j (hVo j) (hVt j) hbd (hball hy)
  have hup : molli ρ t (R.trunc K j) (R.chart j x) ≤ max B 0 := by
    have h1 := ReciprocityTheory.AnForm.A.molli_le_polyMax ρ (hVo j) hpsh ht (z := R.chart j x) hball
    refine h1.trans (ReciprocityTheory.AnForm.A.polyMax_le' ht.le fun y hy => ?_)
    exact (hbd y (hball hy)).trans (max_le_max le_rfl (by linarith))
  have hphReg : R.phReg ρ K t j x = molli ρ t (R.trunc K j) (R.chart j x) - R.q j (R.chart j x) := rfl
  refine ⟨?_, ?_, fun hY => ?_⟩
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  ·
    have hA : R.chart j x ∉ coordDiv (R.S j) := (R.mem_Yo j x hxs).1 hY
    have htr : R.trunc K j (R.chart j x) = max (R.u j (R.chart j x)) (-K) := by
      simp only [RegChartData.trunc, limsupExt, if_neg hA]
    have hu : R.u j (R.chart j x) = R.q j (R.chart j x) + R.ph x := by
      simp only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hxs]
    have hle := ReciprocityTheory.AnForm.A.le_molli ρ (hVo j) hpsh ht (z := R.chart j x) hball
    rw [hphReg]
    linarith [le_max_left (R.u j (R.chart j x)) (-K)]

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PMaxOscillation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric

noncomputable section

theorem PolyMaxOscillation.proof (h0 : ReciprocityTheory.AnForm.A.PolyMaxLogConvexStatement) :
    PolyMaxOscillation.Statement := by
  intro D U u z δ t C₁ hU hu hδ ht hC hCt
  have hC0 : 0 < C₁ := by linarith
  have hb0 : 0 < C₁ * t := mul_pos hC0 ht
  have hδ0 : 0 < δ := hb0.trans hCt
  have hconv := (h0 D U u z δ hU hu hδ0 hδ).1
  have ha0 : 0 < t / (4 * C₁) := by positivity
  have hab : t / (4 * C₁) < C₁ * t := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have key := hconv.slope_mono_adjacent
    (Set.mem_Iic.2 (Real.log_le_log ha0 (hab.trans hCt).le)) (Set.mem_Iic.2 le_rfl)
    (Real.log_lt_log ha0 hab) (Real.log_lt_log hb0 hCt)
  simp only [Real.exp_log ha0, Real.exp_log hb0, Real.exp_log hδ0] at key
  have h1 : Real.log (C₁ * t) - Real.log (t / (4 * C₁)) = Real.log (4 * C₁ ^ 2) := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    congr 1
    field_simp
  have h2 : Real.log δ - Real.log (C₁ * t) = Real.log (δ / (C₁ * t)) :=
    (Real.log_div hδ0.ne' hb0.ne').symm
  have hL1 : 0 < Real.log (4 * C₁ ^ 2) := by
    rw [← h1]
    exact sub_pos.2 (Real.log_lt_log ha0 hab)
  rw [h1, h2, div_le_iff₀ hL1] at key
  rw [mul_div_assoc, mul_comm (Real.log (4 * C₁ ^ 2))]
  exact key

theorem PolyMaxOscillation.proof_closed : PolyMaxOscillation.Statement :=
  PolyMaxOscillation.proof ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
end

