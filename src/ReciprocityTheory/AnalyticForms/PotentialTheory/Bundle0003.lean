module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

theorem analyticSubset_chart_local {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {S : Set X} (hS : A.IsAnalyticSubset S) (hint : interior S = ∅) (j : Fin A.n)
    {z : Fin e → ℂ} (hz : z ∈ (A.chart j) '' (S ∩ (A.chart j).source)) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ (A.chart j) '' (S ∩ (A.chart j).source) ∩ W, f w = 0 := by
  obtain ⟨x, ⟨-, hxs⟩, rfl⟩ := hz
  obtain ⟨W₀, hW₀, hxW₀, r, f, hf, hSW⟩ := hS x
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀) :=
    (A.chart j).isOpen_inter_preimage_symm hW₀
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀ := by
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ W₀
    rw [(A.chart j).left_inv hxs]
    exact hxW₀
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hopen _ hmem

  have hex : ∃ i, ∃ w ∈ Metric.ball ((A.chart j) x) ε, f i ((A.chart j).symm w) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (A.chart j).symm '' Metric.ball ((A.chart j) x) ε ⊆ S := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' := hε hw
      have hin : (A.chart j).symm w ∈ S ∩ W₀ := by
        rw [hSW]
        exact ⟨hw'.2, fun i => hcon i w hw⟩
      exact hin.1
    have hop : IsOpen ((A.chart j).symm '' Metric.ball ((A.chart j) x) ε) :=
      (A.chart j).symm.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun w hw => (hε hw).1)
    have hint' : (A.chart j).symm ((A.chart j) x) ∈ interior S :=
      interior_maximal hsub hop ⟨_, Metric.mem_ball_self hε0, rfl⟩
    rw [hint] at hint'
    exact hint'
  obtain ⟨i, w₀, hw₀, hfw₀⟩ := hex
  refine ⟨Metric.ball ((A.chart j) x) ε, Metric.isOpen_ball, Metric.mem_ball_self hε0,
    (convex_ball _ _).isPreconnected, f i ∘ (A.chart j).symm, ?_, ⟨w₀, hw₀, hfw₀⟩, ?_⟩
  · exact (hf i j).mono hε
  · rintro w ⟨⟨y, ⟨hyS, hys⟩, rfl⟩, hw⟩
    have hw' := hε hw
    have hin : (A.chart j).symm ((A.chart j) y) ∈ S ∩ W₀ :=
      ⟨by rw [(A.chart j).left_inv hys]; exact hyS, hw'.2⟩
    rw [hSW] at hin
    exact hin.2 i

theorem analyticNull : AnalyticNullStatement := by
  intro e X _ A S hS hint j
  exact ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _
    (fun z hz => analyticSubset_chart_local A hS hint j hz)

theorem integralWith_congr_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) {S : Set X} (hS : A.IsAnalyticSubset S)
    (hint : interior S = ∅) {g g' : X → ℝ} (hg : ∀ x ∉ S, g x = g' x) :
    integralWith A P Φ g = integralWith A P Φ g' := by
  first
  | unfold integralWith
  | simp only [integralWith]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hnull : volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0 :=
    analyticNull A S hS hint j
  have hsub : {y | ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y)} ∩
      (A.chart j).target ⊆ (A.chart j) '' (S ∩ (A.chart j).source) := by
    intro y hy
    have hne : ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
        P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y) := hy.1
    have hyt : y ∈ (A.chart j).target := hy.2
    refine ⟨(A.chart j).symm y, ⟨?_, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩
    by_contra hnS
    apply hne
    rw [hg _ hnS]
  have hae : ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y := by
    rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply' hT]
    exact MeasureTheory.measure_mono_null hsub hnull
  exact MeasureTheory.integral_congr_ae hae

theorem mIntCongrNull : MIntCongrNullStatement := by
  unfold MIntCongrNullStatement
  intro e X _ A Φ S hS hint g g' hg
  unfold mInt
  split_ifs with h
  · exact integralWith_congr_null A h.some Φ hS hint hg
  · rfl

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def SmoothOnAlgStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U V : Set X) (f g : X → ℝ)
    (c : ℝ), A.SmoothOn U f → A.SmoothOn V g → V ⊆ U →
      A.SmoothOn V (fun x => f x + g x) ∧ A.SmoothOn U (fun x => c * f x)

theorem smoothOnAlg : SmoothOnAlgStatement := by
  intro e X _ A U V f g c hf hg hVU
  refine ⟨fun j => ?_, fun j => ?_⟩
  · exact ((hf j).mono (by exact fun y hy => ⟨hy.1, hVU hy.2⟩)).add (hg j)
  · exact contDiffOn_const.mul (hf j)

section SlopeTestRemainingChoices

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem add_U (P Q : LocPot X) (x : X) : (P + Q).U x = P.U x ∩ Q.U x := rfl

theorem add_φ (P Q : LocPot X) (x : X) : (P + Q).φ x = fun y => P.φ x y + Q.φ x y := rfl

theorem contDiffAt_of_isPotential (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) y :=
  (hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)

theorem holoOn_add (A : FinHolAtlas e X) {W₁ W₂ : Set X} {G₁ G₂ : X → ℂ}
    (h₁ : A.HoloOn W₁ G₁) (h₂ : A.HoloOn W₂ G₂) :
    A.HoloOn (W₁ ∩ W₂) (fun z => G₁ z + G₂ z) := fun j w hw =>
  ((h₁ j w ⟨hw.1, hw.2.1⟩).add (h₂ j w ⟨hw.1, hw.2.2⟩))

theorem holoOn_mul (A : FinHolAtlas e X) {W : Set X} {G : X → ℂ} (h : A.HoloOn W G) (c : ℂ) :
    A.HoloOn W (fun z => c * G z) := fun j w hw => analyticAt_const.mul (h j w hw)

theorem isPotential_mul (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (c : ℝ)
    (Q : LocPot X) (hU : Q.U = P.U) (hφ : ∀ x y, Q.φ x y = c * P.φ x y) : IsPotential A Q := by
  have hQφ : ∀ x, Q.φ x = fun y => c * P.φ x y := fun x => funext (hφ x)
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [hQφ x, hU]
    exact fun j => contDiffOn_const.mul (hP.1 x j)
  · rw [hU] at hy
    obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hP.2 x x' y hy
    refine ⟨W, hW, hyW, fun z => (c : ℂ) * G z, holoOn_mul A hG c, fun z hz => ?_⟩
    rw [hU] at hz
    rw [hφ, hφ, ← mul_sub, hGe z hz, Complex.re_ofReal_mul]

end SlopeTestRemainingChoices

theorem isPotentialAdd : IsPotentialAddStatement := by
  intro e X _ A P Q hP hQ
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [add_U, add_φ]
    exact fun j => ((hP.1 x j).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add
      ((hQ.1 x j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rw [add_U, add_U] at hy
    obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W₁, hW₁, hyW₁, G₁, hG₁, hGe₁⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W₂, hW₂, hyW₂, G₂, hG₂, hGe₂⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hyW₁, hyW₂⟩, fun z => G₁ z + G₂ z, holoOn_add A hG₁ hG₂,
      fun z hz => ?_⟩
    rw [add_U, add_U] at hz
    obtain ⟨⟨⟨hz₁, hz₂⟩, hzP, hzQ⟩, hzP', hzQ'⟩ := hz
    have e₁ := hGe₁ z ⟨⟨hz₁, hzP⟩, hzP'⟩
    have e₂ := hGe₂ z ⟨⟨hz₂, hzQ⟩, hzQ'⟩
    simp only [add_φ, Complex.add_re]
    linarith

theorem isPotentialZsmul : IsPotentialZsmulStatement := by
  intro e X _ A m P hP
  exact isPotential_mul A P hP (m : ℝ) (P.zsmul m) rfl (fun _ _ => rfl)

theorem isPotentialRsmul : IsPotentialRsmulStatement := by
  intro e X _ A c P hP
  exact isPotential_mul A P hP c (P.rsmul c) rfl (fun _ _ => rfl)

private theorem eventually_chart_symm_chart_comp_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (h : Y → X) (hh : Continuous h)
    (j : Fin B.n) (k : Fin A.n) {w : Fin e' → ℂ} (hw : w ∈ (B.chart j).target)
    (hk : h ((B.chart j).symm w) ∈ (A.chart k).source) :
    ∀ᶠ w' in 𝓝 w, (A.chart k).symm (A.chart k (h ((B.chart j).symm w'))) = h ((B.chart j).symm w') := by
  have hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh)
  filter_upwards [hO.mem_nhds ⟨hw, hk⟩] with w' hw'
  exact (A.chart k).left_inv hw'.2

theorem isPotentialPullback : IsPotentialPullbackStatement := by
  intro e e' X Y _ _ A B h hh P hP
  refine ⟨fun y j w hw => ?_, fun y y' z hz => ?_⟩
  · obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U (h y) := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ P.U (h y)
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hf := contDiffAt_of_isPotential A P hP (h y) k hin
    have hg : ContDiffAt ℝ ∞ (A.chart k ∘ h ∘ (B.chart j).symm) w :=
      (AnalyticAt.contDiffAt (n := ∞) (hh.2 j k w ⟨hw.1, hk⟩)).restrict_scalars ℝ
    refine (ContDiffAt.congr_of_eventuallyEq (hf.comp w hg) ?_).contDiffWithinAt
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show P.φ (h y) (h ((B.chart j).symm w')) =
      P.φ (h y) ((A.chart k).symm (A.chart k (h ((B.chart j).symm w'))))
    rw [hw']
  · have hz' : h z ∈ P.U (h y) ∩ P.U (h y') := hz
    obtain ⟨W, hW, hzW, G, hG, hGe⟩ := hP.2 (h y) (h y') (h z) hz'
    refine ⟨h ⁻¹' W, hW.preimage hh.1, hzW, G ∘ h, fun j w hw => ?_, fun z' hz' => hGe (h z') hz'⟩
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm w))
    have hin : A.chart k (h ((B.chart j).symm w)) ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' W := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      show (A.chart k).symm (A.chart k (h ((B.chart j).symm w))) ∈ W
      rw [(A.chart k).left_inv hk]
      exact hw.2
    have hc : AnalyticAt ℂ ((G ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (B.chart j).symm)) w :=
      AnalyticAt.comp (hG k _ hin) (hh.2 j k w ⟨hw.1, hk⟩)
    refine hc.congr ?_
    filter_upwards [eventually_chart_symm_chart_comp_eq A B h hh.1 j k hw.1 hk] with w' hw'
    show G ((A.chart k).symm (A.chart k (h ((B.chart j).symm w')))) = G (h ((B.chart j).symm w'))
    rw [hw']

private theorem eventually_contDiffAt_potential_chart_symm {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) z := by
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy] with z hz
  exact contDiffAt_of_isPotential A P hP x j hz

private theorem differentiableAt_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ F y :=
  hF.differentiableAt (by simp)

private theorem differentiableAt_fderiv_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ (fderiv ℝ F) y :=
  (hF.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)

private theorem fderiv_fderiv_add' {n : ℕ} {F G : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (hG : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ G z) :
    fderiv ℝ (fderiv ℝ (fun z => F z + G z)) y = fderiv ℝ (fderiv ℝ F) y + fderiv ℝ (fderiv ℝ G) y := by
  have hev : fderiv ℝ (fun z => F z + G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + fderiv ℝ G z := by
    filter_upwards [hF, hG] with z hFz hGz
    exact fderiv_add (differentiableAt_of_contDiffAt_infty hFz) (differentiableAt_of_contDiffAt_infty hGz)
  rw [hev.fderiv_eq]
  exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds)
    (differentiableAt_fderiv_of_contDiffAt_infty hG.self_of_nhds)

theorem isPshAdd : IsPshAddStatement := by
  intro e X _ A P Q hP hQ hpP hpQ x j y hy w
  have hy' : y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ P.U x ∩ Q.U x := hy
  have hyP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := ⟨hy'.1, hy'.2.1⟩
  have hyQ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x := ⟨hy'.1, hy'.2.2⟩
  have hp := hpP x j y hyP w
  have hq := hpQ x j y hyQ w
  have hrw : (P + Q).φ x ∘ (A.chart j).symm =
      fun z => (P.φ x ∘ (A.chart j).symm) z + (Q.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp hq ⊢
  rw [fderiv_fderiv_add' (eventually_contDiffAt_potential_chart_symm A P hP x j hyP)
    (eventually_contDiffAt_potential_chart_symm A Q hQ x j hyQ)]
  simp only [ContinuousLinearMap.add_apply]
  linarith

private theorem fderiv_fderiv_const_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => c * F z)) y = c • fderiv ℝ (fderiv ℝ F) y := by
  have hev : fderiv ℝ (fun z => c * F z) =ᶠ[𝓝 y] fun z => c • fderiv ℝ F z := by
    filter_upwards [hF] with z hFz
    exact fderiv_const_mul (differentiableAt_of_contDiffAt_infty hFz) c
  rw [hev.fderiv_eq]
  exact fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds) c

theorem isPshRsmul : IsPshRsmulStatement := by
  intro e X _ A c P hc hP hpP x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := hy
  have hp := hpP x j y hy' w
  have hrw : (P.rsmul c).φ x ∘ (A.chart j).symm = fun z => c * (P.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp ⊢
  rw [fderiv_fderiv_const_mul (eventually_contDiffAt_potential_chart_symm A P hP x j hy') c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [show ∀ a b : ℝ, (c * a + c * b) / 4 = c * ((a + b) / 4) from fun a b => by ring]
  exact mul_nonneg hc hp

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
section
namespace ReciprocityTheory.AnForm.M

open FinHolAtlas

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoMap_id (A : FinHolAtlas e X) : HoloMap A A id :=
  ⟨continuous_id, fun j k => A.holo j k⟩

theorem isAnalyticSubset_empty (A : FinHolAtlas e X) : A.IsAnalyticSubset ∅ := by
  intro x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, 1, fun _ _ => (1 : ℂ), ?_, ?_⟩
  · intro i j
    exact analyticOnNhd_const
  · ext y
    simp

theorem det_fderiv_transition_ne_zero (A : FinHolAtlas e X) (j k : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (A.chart k).source) :
    LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hyU : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := ⟨hy, hk⟩
  have hfd : DifferentiableAt ℂ (A.chart k ∘ (A.chart j).symm) y :=
    (A.holo j k y hyU).differentiableAt
  have hz : (A.chart k ∘ (A.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source := by
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
    rw [(A.chart k).left_inv hk]
    exact (A.chart j).map_target hy
  have hgd : DifferentiableAt ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y) :=
    (A.holo k j _ hz).differentiableAt
  have hev : (A.chart j ∘ (A.chart k).symm) ∘ (A.chart k ∘ (A.chart j).symm) =ᶠ[nhds y] id := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    show (A.chart j) ((A.chart k).symm ((A.chart k) ((A.chart j).symm y'))) = y'
    rw [(A.chart k).left_inv hy'.2, (A.chart j).right_inv hy'.1]
  have hcomp : (fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)).comp
      (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    rw [← fderiv_comp y hgd hfd, hev.fderiv_eq, fderiv_id]
  intro h0
  have hdet : LinearMap.det (((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).comp
      ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) = 1 := by
    have hc : ((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).comp ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
        (((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)).comp (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := rfl
    rw [hc, hcomp, ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [LinearMap.det_comp, h0, mul_zero] at hdet
  exact zero_ne_one hdet

theorem isDegreeOff_id (A : FinHolAtlas e X) : IsDegreeOff A A id 1 ∅ := by
  refine ⟨isAnalyticSubset_empty A, interior_empty, ?_, ?_, ?_, ?_⟩
  · rw [Set.preimage_id]
    exact isAnalyticSubset_empty A
  · rw [Set.preimage_id]
    exact interior_empty
  · intro x _
    rw [Set.preimage_id]
    exact Set.ncard_singleton x
  · intro j k y hy _ hk
    rw [Function.id_comp]
    exact det_fderiv_transition_ne_zero A j k hy hk

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem pa_holoSmooth {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ))
    (hF : AnalyticOnNhd ℂ F U) : ContDiffOn ℝ ∞ F U :=
  fun x hx => ((hF x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

def pa_aff {e : ℕ} (a : ℂ) (ha : a ≠ 0) (b : Fin e → ℂ) : (Fin e → ℂ) ≃ₜ (Fin e → ℂ) where
  toFun y := a • (y - b)
  invFun z := a⁻¹ • z + b
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ ha]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem pa_aff_analytic {e : ℕ} (a : ℂ) (b : Fin e → ℂ) (y : Fin e → ℂ) :
    AnalyticAt ℂ (fun y : Fin e → ℂ => a • (y - b)) y :=
  by fun_prop

theorem pa_compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (s : Set X)
    (hs : IsOpen s) : IsCompatChart A (ψ.restrOpen s hs) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1, hx2.1⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.1, hx2⟩

theorem pa_compat_aff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (a : ℂ) (ha : a ≠ 0)
    (b : Fin e → ℂ) : IsCompatChart A (ψ.transHomeomorph (pa_aff a ha b)) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨fun z hz => (pa_aff_analytic a b _).comp (h1 z hz), fun z hz => ?_⟩
  have hinv : AnalyticAt ℂ (fun z : Fin e → ℂ => a⁻¹ • z + b) z :=
    by fun_prop
  exact AnalyticAt.comp (f := fun w : Fin e → ℂ => a⁻¹ • w + b) (h2 (a⁻¹ • z + b) hz) hinv

theorem existsPartition : ExistsPartitionStatement := by
  intro e X _ _ _ A
  obtain ⟨χ, h0, h1, h2, h3⟩ := ReciprocityTheory.AnForm.exists_chart_partition A.chart A.cover
    (fun i j => pa_holoSmooth _ _ (A.holo i j))
  exact ⟨⟨χ, fun j k => (h3 j k).mono Set.inter_subset_left, h0, h2, h1⟩⟩

def AtlasOfCompatStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (ψ : Fin m → OpenPartialHomeomorph X (Fin e → ℂ)), (∀ i, IsCompatChart A (ψ i)) →
    (∀ x, ∃ i, x ∈ (ψ i).source) →
    ∃ B : FinHolAtlas e X, A.Compatible B ∧ (∀ i, ∃ j, B.chart j = ψ i) ∧ ∀ j, ∃ i, B.chart j = ψ i

theorem atlasOfCompat : AtlasOfCompatStatement := by
  intro e X _ A m ψ hψ hcov
  refine ⟨⟨m, ψ, hcov, ?_⟩, ⟨fun j k => (hψ k j).1, fun j k => (hψ j k).2⟩, fun i => ⟨i, rfl⟩,
    fun j => ⟨j, rfl⟩⟩
  intro j k z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨l, hx⟩ := A.cover ((ψ j).symm z)
  have hev : ∀ᶠ w in nhds z, (ψ j).symm w ∈ (A.chart l).source :=
    ((ψ j).continuousAt_symm hz1).preimage_mem_nhds ((A.chart l).open_source.mem_nhds hx)
  have ha1 := (hψ k l).1 (A.chart l ((ψ j).symm z))
    ⟨(A.chart l).map_source hx, by rw [Set.mem_preimage, (A.chart l).left_inv hx]; exact hz2⟩
  have ha2 := (hψ j l).2 z ⟨hz1, hx⟩
  exact (AnalyticAt.comp (f := ⇑(A.chart l) ∘ ⇑(ψ j).symm) ha1 ha2).congr (hev.mono fun w hw => by
    simp only [Function.comp, (A.chart l).left_inv hw])

end

end ReciprocityTheory.AnForm.M
end

