module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjLineChartsNotSubsetBall
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.RegMaxReindex
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (contDiffOn_compat analyticAt_compat)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

namespace ChartLeviThGe

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem compat_chart (A : FinHolAtlas D X) (a : Fin A.n) : IsCompatChart A (A.chart a) :=
  fun j => ⟨A.holo j a, A.holo a j⟩

theorem eventuallyEq_comp_chart {β : Type*} (h : X → β) (ψ χ : OpenPartialHomeomorph X (Fin D → ℂ))
    {y : Fin D → ℂ} (hy : y ∈ χ.target) (hs : χ.symm y ∈ ψ.source) :
    h ∘ χ.symm =ᶠ[𝓝 y] (h ∘ ψ.symm) ∘ (ψ ∘ χ.symm) := by
  filter_upwards [(χ.continuousAt_symm hy).preimage_mem_nhds (ψ.open_source.mem_nhds hs)]
    with z hz
  simp [Function.comp, ψ.left_inv hz]

theorem contDiffAt_comp_symm {U : Set X} (hU : IsOpen U) {h : X → ℝ} (hh : A.SmoothOn U h)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {p : X} (hpU : p ∈ U)
    (hpψ : p ∈ ψ.source) : ContDiffAt ℝ 2 (h ∘ ψ.symm) (ψ p) := by
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' U) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target hU
  exact ((contDiffOn_compat hψ hU hh).contDiffAt
    (hO.mem_nhds ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using hpU⟩)).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem analyticAt_comp_compat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {F : X → E} {a : Fin A.n}
    {p : X} (hpa : p ∈ (A.chart a).source) (hpψ : p ∈ ψ.source)
    (hF : AnalyticAt ℂ (F ∘ (A.chart a).symm) (A.chart a p)) :
    AnalyticAt ℂ (F ∘ ψ.symm) (ψ p) := by
  have h1 : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using hpa⟩
  have h2 : AnalyticAt ℂ ((F ∘ (A.chart a).symm) ∘ (A.chart a ∘ ψ.symm)) (ψ p) :=
    hF.comp_of_eq h1 (by simp [ψ.left_inv hpψ])
  refine h2.congr ?_
  filter_upwards [(ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
    (by rw [ψ.left_inv hpψ]; exact (A.chart a).open_source.mem_nhds hpa)] with z hz
  simp [Function.comp, (A.chart a).left_inv hz]

theorem fderiv_compat_eq_zero {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ)
    {a : Fin A.n} {p : X} (ha : p ∈ (A.chart a).source) (hpψ : p ∈ ψ.source) {v : Fin D → ℂ}
    (h : fderiv ℂ (A.chart a ∘ ψ.symm) (ψ p) v = 0) : v = 0 := by
  have hu : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using ha⟩
  have huy : (A.chart a ∘ ψ.symm) (ψ p) = A.chart a p := by simp [ψ.left_inv hpψ]
  have ht : AnalyticAt ℂ (ψ ∘ (A.chart a).symm) ((A.chart a ∘ ψ.symm) (ψ p)) := by
    rw [huy]; exact analyticAt_compat hψ a ha hpψ
  have hid : (ψ ∘ (A.chart a).symm) ∘ (A.chart a ∘ ψ.symm) =ᶠ[𝓝 (ψ p)] id := by
    filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hpψ),
      (ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
        (by rw [ψ.left_inv hpψ]; exact (A.chart a).open_source.mem_nhds ha)] with z hz1 hz2
    simp [Function.comp, (A.chart a).left_inv hz2, ψ.right_inv hz1]
  have hD := fderiv_comp (ψ p) ht.differentiableAt hu.differentiableAt
  rw [hid.fderiv_eq, fderiv_id] at hD
  have := congrArg (fun L => L v) hD
  simpa [h] using this

variable {om : LocPot X}

theorem levi_base_indep (hpot : IsPotential A om) {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
    (hψ : IsCompatChart A ψ) {x x' p : X} (hx : p ∈ om.U x) (hx' : p ∈ om.U x')
    (hpψ : p ∈ ψ.source) (v : Fin D → ℂ) :
    levi (om.φ x ∘ ψ.symm) (ψ p) v = levi (om.φ x' ∘ ψ.symm) (ψ p) v := by
  obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := hpot.2 x x' p ⟨hx, hx'⟩
  obtain ⟨a, ha⟩ := A.cover p
  have hGa : AnalyticAt ℂ (G ∘ ψ.symm) (ψ p) :=
    analyticAt_comp_compat hψ ha hpψ
      (hG a _ ⟨(A.chart a).map_source ha, by simpa [(A.chart a).left_inv ha] using hpW⟩)
  have hN : W ∩ om.U x ∩ om.U x' ∈ 𝓝 p :=
    ((hWo.inter (om.isOpen_U x)).inter (om.isOpen_U x')).mem_nhds ⟨⟨hpW, hx⟩, hx'⟩
  have hev : om.φ x ∘ ψ.symm =ᶠ[𝓝 (ψ p)]
      fun z => (om.φ x' ∘ ψ.symm) z + 1 * (G (ψ.symm z)).re := by
    filter_upwards [(ψ.continuousAt_symm (ψ.map_source hpψ)).preimage_mem_nhds
      (by rwa [ψ.left_inv hpψ])] with z hz
    have := hEq _ hz
    simp only [Function.comp]
    linarith
  have hre : ContDiffAt ℝ 2 (fun z => (G (ψ.symm z)).re) (ψ p) := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp (ψ p)
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have h0 : levi (fun z => (G (ψ.symm z)).re) (ψ p) v = 0 := levi_re_analytic hGa v
  rw [levi_congr hev v, levi_add_smul 1
    (contDiffAt_comp_symm (om.isOpen_U x') (hpot.1 x') hψ hx' hpψ) hre v, h0]
  ring

theorem levi_pos_compat (hpot : IsPotential A om) (hpos : IsPosPot A om)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {x p : X}
    (hpx : p ∈ om.U x) (hpψ : p ∈ ψ.source) {v : Fin D → ℂ} (hv : v ≠ 0) :
    0 < levi (om.φ x ∘ ψ.symm) (ψ p) v := by
  obtain ⟨a, ha⟩ := A.cover p
  have hu : AnalyticAt ℂ (A.chart a ∘ ψ.symm) (ψ p) :=
    (hψ a).2 _ ⟨ψ.map_source hpψ, by simpa [ψ.left_inv hpψ] using ha⟩
  have huy : (A.chart a ∘ ψ.symm) (ψ p) = A.chart a p := by simp [ψ.left_inv hpψ]
  have hev := eventuallyEq_comp_chart (om.φ x) (A.chart a) ψ (ψ.map_source hpψ)
    (by rwa [ψ.left_inv hpψ])
  have hcd : ContDiffAt ℝ 2 (om.φ x ∘ (A.chart a).symm) ((A.chart a ∘ ψ.symm) (ψ p)) := by
    rw [huy]; exact contDiffAt_comp_symm (om.isOpen_U x) (hpot.1 x) (compat_chart A a) hpx ha
  rw [levi_congr hev v, levi_comp v hu hcd, huy]
  refine hpos x a _ ⟨(A.chart a).map_source ha, by simpa [(A.chart a).left_inv ha] using hpx⟩ _ ?_
  intro h0
  exact hv (fderiv_compat_eq_zero hψ ha hpψ h0)

theorem continuousAt_levi_self (hpot : IsPotential A om) {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
    (hψ : IsCompatChart A ψ) {p0 : X} (hp0 : p0 ∈ ψ.source) (v0 : Fin D → ℂ) :
    ContinuousAt (fun q : X × (Fin D → ℂ) => levi (om.φ q.1 ∘ ψ.symm) (ψ q.1) q.2) (p0, v0) := by
  have hV : IsOpen (ψ.target ∩ ψ.symm ⁻¹' om.U p0) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (om.isOpen_U p0)
  have hcd : ContDiffOn ℝ 2 (om.φ p0 ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' om.U p0) :=
    (contDiffOn_compat hψ (om.isOpen_U p0) (hpot.1 p0)).of_le (WithTop.coe_le_coe.2 le_top)
  have hc := continuousOn_levi hV hcd
  have hmem : (ψ p0, v0) ∈ (ψ.target ∩ ψ.symm ⁻¹' om.U p0) ×ˢ (Set.univ : Set (Fin D → ℂ)) :=
    ⟨⟨ψ.map_source hp0, by simpa [ψ.left_inv hp0] using om.mem_U p0⟩, trivial⟩
  have h1 : ContinuousAt (fun r : (Fin D → ℂ) × (Fin D → ℂ) => levi (om.φ p0 ∘ ψ.symm) r.1 r.2)
      (ψ p0, v0) := hc.continuousAt ((hV.prod isOpen_univ).mem_nhds hmem)
  have h2 : ContinuousAt (fun q : X × (Fin D → ℂ) => (ψ q.1, q.2)) (p0, v0) :=
    ((ψ.continuousAt hp0).comp continuousAt_fst).prodMk continuousAt_snd
  refine (ContinuousAt.comp (g := fun r : (Fin D → ℂ) × (Fin D → ℂ) => levi (om.φ p0 ∘ ψ.symm) r.1 r.2)
    (f := fun q : X × (Fin D → ℂ) => (ψ q.1, q.2)) h1 h2).congr ?_
  have hN : (om.U p0 ∩ ψ.source) ×ˢ (Set.univ : Set (Fin D → ℂ)) ∈ 𝓝 (p0, v0) :=
    (((om.isOpen_U p0).inter ψ.open_source).prod isOpen_univ).mem_nhds ⟨⟨om.mem_U p0, hp0⟩, trivial⟩
  filter_upwards [hN] with q hq
  exact (levi_base_indep hpot hψ (om.mem_U q.1) hq.1.1 hq.1.2 q.2).symm

theorem exists_levi_lower (hpot : IsPotential A om) (hpos : IsPosPot A om)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {K : Set X}
    (hK : IsCompact K) (hKs : K ⊆ ψ.source) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ x, p ∈ om.U x → ∀ v : Fin D → ℂ,
      c * ‖v‖ ^ 2 ≤ levi (om.φ x ∘ ψ.symm) (ψ p) v := by
  have hunit : ∀ v : Fin D → ℂ, v ≠ 0 → ‖‖v‖⁻¹ • v‖ = 1 := fun v hv => by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  by_cases hne : (K ×ˢ sphere (0 : Fin D → ℂ) 1).Nonempty
  · have hcont : ContinuousOn (fun q : X × (Fin D → ℂ) => levi (om.φ q.1 ∘ ψ.symm) (ψ q.1) q.2)
        (K ×ˢ sphere (0 : Fin D → ℂ) 1) := fun q hq =>
      (continuousAt_levi_self hpot hψ (hKs hq.1) q.2).continuousWithinAt
    obtain ⟨q1, hq1, hmin⟩ := (hK.prod (isCompact_sphere 0 1)).exists_isMinOn hne hcont
    have hq1v : q1.2 ≠ 0 := by
      intro h0
      have := hq1.2
      rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
      exact zero_ne_one this
    refine ⟨_, levi_pos_compat hpot hpos hψ (om.mem_U q1.1) (hKs hq1.1) hq1v, ?_⟩
    intro p hp x hx v
    rw [levi_base_indep hpot hψ hx (om.mem_U p) (hKs hp) v]
    by_cases hv : v = 0
    · subst hv; simp [levi_zero]
    have hm := isMinOn_iff.1 hmin (p, ‖v‖⁻¹ • v) ⟨hp, by rw [mem_sphere_zero_iff_norm]; exact hunit v hv⟩
    have hw : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]
    have hs : levi (om.φ p ∘ ψ.symm) (ψ p) v =
        ‖v‖ ^ 2 * levi (om.φ p ∘ ψ.symm) (ψ p) (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hw]
      exact levi_smul_dir _ _ _ _
    rw [hs, mul_comm]
    exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  · refine ⟨1, one_pos, fun p hp x hx v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp [levi_zero]
    exact absurd ⟨(p, ‖v‖⁻¹ • v), hp, by rw [mem_sphere_zero_iff_norm]; exact hunit v hv⟩ hne

end ChartLeviThGe


end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)

noncomputable section

namespace RegChartData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)


open Classical in
theorem glue_eventually (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      R.regularised ρ K t ε η y =
        regMax ε (fun j : {j // x₀ ∈ R.mid j} => R.phReg ρ K t j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, (x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      (x₀ ∉ R.mid j → y ∉ L j ∧ y ∉ closure (R.inner j)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases h : x₀ ∈ R.mid j
    · filter_upwards [(R.isOpen_mid j).mem_nhds h] with y hy
      exact ⟨fun _ => hy, fun h' => absurd h h'⟩
    · have hc : IsOpen (L j ∪ closure (R.inner j))ᶜ :=
        ((hLc j).union isClosed_closure).isOpen_compl
      have hx : x₀ ∈ (L j ∪ closure (R.inner j))ᶜ := by
        rintro (h1 | h1)
        · exact h (hLsub j h1)
        · exact h (R.closure_inner j h1)
      filter_upwards [hc.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_union, not_or] at hy
      exact ⟨fun h' => absurd h' h, fun _ => hy⟩
  filter_upwards [hev] with y hy
  refine ⟨fun j hj => (hy j).1 hj, ?_⟩
  simp only [RegChartData.regularised, PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine regMax_of_injective
    (fun j : {j // x₀ ∈ R.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ R.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := R.cover y
  have hk0 : x₀ ∈ R.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ R.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, R.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith

theorem arg_contDiffAt (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin R.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ R.mid j) :
    ContDiffAt ℝ ∞ (fun y => R.phReg ρ K t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by
  have hxj : x ∈ (R.chart j).source := R.mid_subset_source j hj
  have hT : ContDiffAt ℝ ∞ (R.chart j ∘ ψ.symm) (ψ x) :=
    ((analyticAt_transition hψ (R.compat j) hx hxj).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hTx : (R.chart j ∘ ψ.symm) (ψ x) = R.chart j x := by simp [ψ.left_inv hx]
  have hS := (R.smoothed_local ρ K ht j (hball j x (subset_closure hj))).1
  have hq : ContDiffAt ℝ ∞ (R.q j) (R.chart j x) :=
    (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds ((R.chart j).map_source hxj))
  rw [← hTx] at hS hq
  have hη := contDiffAt_comp_symm_of_smoothOn hψ (R.isOpen_mid j) (hcut.smooth j) hj hx
  exact ((hS.comp (ψ x) hT).sub (hq.comp (ψ x) hT)).add (contDiffAt_const.mul hη)

end RegChartData


open Classical in
theorem GlueRegularised.proof : GlueRegularised.Statement := by
  intro X _ _ _ D A R ρ η Cη K t ε hcut ht hε hball hcmp
  refine ⟨fun i y hy => ?_, fun k x hx w => ?_⟩
  ·
    have hyt : y ∈ (A.chart i).target := hy.1
    have hx₀ : (A.chart i).symm y ∈ (A.chart i).source := (A.chart i).map_target hyt
    have hψ : IsCompatChart A (A.chart i) := fun l => ⟨A.holo l i, A.holo i l⟩
    have hyx : A.chart i ((A.chart i).symm y) = y := (A.chart i).right_inv hyt
    have hloc := R.glue_eventually ρ η hcut hε.le hcmp ((A.chart i).symm y)
    have hG : ContDiffAt ℝ ∞ (fun y' => regMax ε (fun j : {j // (A.chart i).symm y ∈ R.mid j} =>
        R.phReg ρ K t j ((A.chart i).symm y') + 4 * ε * η j ((A.chart i).symm y')) + ε / 2) y := by
      have hr := ((ReciprocityTheory.AnForm.A.regMax_thm {j // (A.chart i).symm y ∈ R.mid j}).1 ε hε).1
      refine (hr.contDiffAt.comp y (contDiffAt_pi.2 fun j => ?_)).add contDiffAt_const
      have := R.arg_contDiffAt ρ η (K := K) (ε := ε) hcut ht hball hψ hx₀ j.2
      rwa [hyx] at this
    refine (hG.congr_of_eventuallyEq ?_).contDiffWithinAt
    exact (((A.chart i).continuousAt_symm hyt).tendsto.eventually hloc).mono fun y' hy' => hy'.2
  ·
    have hψ := R.compat k
    have hxk : x ∈ (R.chart k).source := R.mid_subset_source k hx
    have hzt : R.chart k x ∈ (R.chart k).target := (R.chart k).map_source hxk
    have hqk : ContDiffAt ℝ ∞ (R.q k) (R.chart k x) :=
      (R.q_smooth k).contDiffAt ((R.chart k).open_target.mem_nhds hzt)
    set b : {j // x ∈ R.mid j} → (Fin D → ℂ) → ℝ := fun j y =>
      R.phReg ρ K t j ((R.chart k).symm y) + 4 * ε * η j ((R.chart k).symm y) + R.q k y with hb_def
    have hb : ∀ j, ContDiffAt ℝ ∞ (b j) (R.chart k x) := fun j =>
      (R.arg_contDiffAt ρ η (K := K) (ε := ε) hcut ht hball hψ hxk j.2).add hqk
    have hadd := ((ReciprocityTheory.AnForm.A.regMax_thm {j // x ∈ R.mid j}).1 ε hε).2.2.2.2.2.2.1
    have hgerm : R.chartFun (R.regularised ρ K t ε η) k =ᶠ[𝓝 (R.chart k x)]
        fun y => regMax ε (fun j => b j y) + ε / 2 := by
      have hloc := R.glue_eventually ρ η hcut hε.le hcmp x
      have ht' : Tendsto (R.chart k).symm (𝓝 (R.chart k x)) (𝓝 x) := by
        have := ((R.chart k).continuousAt_symm hzt).tendsto
        rwa [(R.chart k).left_inv hxk] at this
      filter_upwards [ht'.eventually hloc] with y hy
      simp only [PotentialCharts.chartFun]
      rw [hy.2, hb_def, hadd]
      ring
    have hconst : levi (fun y => regMax ε (fun j => b j y) + ε / 2) (R.chart k x) w =
        levi (fun y => regMax ε (fun j => b j y)) (R.chart k x) w := by
      unfold levi
      have : fderiv ℝ (fun y => regMax ε (fun j => b j y) + ε / 2) =
          fderiv ℝ (fun y => regMax ε (fun j => b j y)) := funext fun _ => fderiv_add_const _
      rw [this]
    rw [levi_congr hgerm w, hconst]
    have hzV : R.chart k x ∈ interior {y | ∀ j, ContDiffAt ℝ 2 (b j) y} :=
      mem_interior_iff_mem_nhds.2 (Filter.eventually_all.2 fun j =>
        ((hb j).of_le (WithTop.coe_le_coe.mpr le_top)).eventually (by simp))
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm D {j // x ∈ R.mid j} ε _ b isOpen_interior hε
      (fun j y hy => (interior_subset hy j).contDiffWithinAt) _ hzV w _ fun ⟨j, hj⟩ => ?_
    have hxj : x ∈ (R.chart j).source := R.mid_subset_source j hj
    set T := R.chart j ∘ (R.chart k).symm with hT
    have hTa : AnalyticAt ℂ T (R.chart k x) := analyticAt_transition hψ (R.compat j) hxk hxj
    have hTR : ContDiffAt ℝ ∞ T (R.chart k x) := (hTa.restrictScalars (𝕜 := ℝ)).contDiffAt
    have hTz : T (R.chart k x) = R.chart j x := by simp [hT, (R.chart k).left_inv hxk]
    obtain ⟨hS, hSl⟩ := R.smoothed_local ρ K ht j (hball j x (subset_closure hj))
    have hq : ContDiffAt ℝ ∞ (R.q j) (R.chart j x) :=
      (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds ((R.chart j).map_source hxj))
    rw [← hTz] at hS hSl hq
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hS2 : ContDiffAt ℝ 2 (R.smoothed ρ K t j ∘ T) (R.chart k x) := (hS.comp _ hTR).of_le h2
    have hQ2 : ContDiffAt ℝ 2 (fun y => R.q k y - R.q j (T y)) (R.chart k x) :=
      (hqk.sub (hq.comp _ hTR)).of_le h2
    have hE2 : ContDiffAt ℝ 2 (η j ∘ (R.chart k).symm) (R.chart k x) :=
      (contDiffAt_comp_symm_of_smoothOn hψ (R.isOpen_mid j) (hcut.smooth j) hj hxk).of_le h2
    have hF2 : ContDiffAt ℝ 2 (fun y => (R.smoothed ρ K t j ∘ T) y + 1 * (R.q k y - R.q j (T y)))
        (R.chart k x) := hS2.add (contDiffAt_const.mul hQ2)
    have hbe : b ⟨j, hj⟩ = fun y => ((R.smoothed ρ K t j ∘ T) y + 1 * (R.q k y - R.q j (T y))) +
        4 * ε * (η j ∘ (R.chart k).symm) y := by
      funext y
      simp only [hb_def, RegChartData.phReg, hT, Function.comp_apply]
      ring
    have e1 := levi_add_smul (4 * ε) hF2 hE2 w
    have e2 := levi_add_smul 1 hS2 hQ2 w
    have e3 := levi_comp (φ := R.smoothed ρ K t j) w hTa (hS.of_le h2)

    have e4 : levi (fun y => R.q k y - R.q j (T y)) (R.chart k x) w = 0 := by
      obtain ⟨W, hWo, hxW, G, hG, hGeq⟩ := R.q_th k x x ⟨R.th.mem_U x, hxk⟩
      obtain ⟨W', hWo', hxW', G', hG', hGeq'⟩ := R.q_th j x x ⟨R.th.mem_U x, hxj⟩
      have hO : IsOpen (W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source) :=
        (((hWo.inter hWo').inter (R.th.isOpen_U x)).inter (R.chart k).open_source).inter
          (R.chart j).open_source
      have hxO : x ∈ W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source :=
        ⟨⟨⟨⟨hxW, hxW'⟩, R.th.mem_U x⟩, hxk⟩, hxj⟩
      have hev1 : ∀ᶠ y in 𝓝 (R.chart k x),
          (R.chart k).symm y ∈ W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source :=
        ((R.chart k).continuousAt_symm hzt).preimage_mem_nhds
          (by rw [(R.chart k).left_inv hxk]; exact hO.mem_nhds hxO)
      have hev := hev1.and ((R.chart k).open_target.mem_nhds hzt)
      have hGa := analyticAt_comp_symm_of_holoOn hψ hG hxW hxk
      have hGa' := analyticAt_comp_symm_of_holoOn hψ hG' hxW' hxk
      have hgerm : (fun y => R.q k y - R.q j (T y)) =ᶠ[𝓝 (R.chart k x)]
          fun y => (((G ∘ (R.chart k).symm) - (G' ∘ (R.chart k).symm)) y).re := by
        filter_upwards [hev] with y hy
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hyt⟩ := hy
        have ek := hGeq _ ⟨⟨h1, h3⟩, h4⟩
        have ej := hGeq' _ ⟨⟨h2, h3⟩, h5⟩
        rw [(R.chart k).right_inv hyt] at ek
        simp only [hT, Function.comp_apply, Pi.sub_apply, Complex.sub_re]
        linarith
      rw [levi_congr hgerm w]
      exact levi_re_analytic (hGa.sub hGa') w
    have hl := hcut.levi_ge j k x ⟨hj, hx⟩ w
    have h4 := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 4 * ε)
    have h0 := hSl (fderiv ℂ T (R.chart k x) w)
    rw [hbe, e1, e2, e3, e4]
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
end

