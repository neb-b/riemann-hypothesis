module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh IsPosPot IsSection logNormSec mInt
  MIntegrable maMeasure maMeasure_thm logNormIntegrable mIntegrableCont)

noncomputable section

theorem continuousAt_of_charts {e : ℕ} {X : Type} [TopologicalSpace X] {E : Type}
    [TopologicalSpace E] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) (g : X → E)
    (hg : ∀ j, ContinuousOn (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  set c := A.chart j
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hmem : c y ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hj, by
    show c.symm (c y) ∈ U
    rw [c.left_inv hj]
    exact hy⟩
  have h1 : ContinuousAt (g ∘ c.symm) (c y) := (hg j).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((g ∘ c.symm) ∘ c) y := h1.comp (c.continuousAt hj)
  refine h2.congr ?_
  filter_upwards [c.open_source.mem_nhds hj] with z hz
  simp [Function.comp, c.left_inv hz]

theorem continuous_secNorm {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous (secNorm L s) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hsc : ContinuousAt (s x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (s x₀)
    (fun j => (hs.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hφc : ContinuousAt (L.φ x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (L.φ x₀)
    (fun j => (hL.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hf : ContinuousAt (fun y => ‖s x₀ y‖ * Real.exp (-L.φ x₀ y)) x₀ :=
    hsc.norm.mul (Real.continuous_exp.continuousAt.comp hφc.neg)
  refine hf.congr ?_
  filter_upwards [(L.isOpen_U x₀).mem_nhds (L.mem_U x₀)] with y hy
  exact hs.2 x₀ y y ⟨hy, L.mem_U y⟩

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (hP : IsPosPot A P) : IsPsh A P := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (hP x j y hy w hw).le

theorem greenEp_nonneg {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (x : W) : 0 ≤ greenEp L s ε x := by
  unfold greenEp
  apply Real.log_nonneg
  have : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  linarith

theorem greenEp_le_one {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : W) : greenEp L s ε x ≤ greenEp L s 1 x := by
  unfold greenEp
  have h0 : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  apply Real.log_le_log (by linarith)
  have : ε / secNorm L s x ^ 2 ≤ 1 / secNorm L s x ^ 2 :=
    div_le_div_of_nonneg_right hε1 (sq_nonneg _)
  linarith

theorem greenEp_one_eq {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) (x : W) :
    greenEp L s 1 x = Real.log (secNorm L s x ^ 2 + 1) - 2 * logNormSec L s x := by
  have hl : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp
  rw [hl]
  by_cases hN : secNorm L s x = 0
  · simp [hN]
  · have h2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hN
    have h3 : secNorm L s x ^ 2 + 1 ≠ 0 := by positivity
    rw [show 1 + 1 / secNorm L s x ^ 2 = (secNorm L s x ^ 2 + 1) / secNorm L s x ^ 2 by
      field_simp, Real.log_div h3 h2, Real.log_pow]
    push_cast
    ring

theorem greenEp_tendsto_zero {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ)
    (x : W) : Tendsto (fun ε => greenEp L s ε x) (𝓝[>] 0) (𝓝 0) := by
  unfold greenEp
  set c := secNorm L s x ^ 2
  have hc : ContinuousAt (fun ε : ℝ => 1 + ε / c) 0 :=
    (continuous_const.add (continuous_id.div_const c)).continuousAt
  have hlog : ContinuousAt (fun ε : ℝ => Real.log (1 + ε / c)) 0 := hc.log (by simp)
  have ht := hlog.tendsto
  simp only [zero_div, add_zero, Real.log_one] at ht
  exact tendsto_nhdsWithin_of_tendsto_nhds ht

theorem GreenMassZero.proof : GreenMassZero.Statement := by
  intro D W _ _ _ S η hη
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set Φ : Fin (D + 1) → LocPot W := fun _ => S.Om.pot with hΦdef
  have hΦ : ∀ i, IsPotential S.A (Φ i) := fun _ => S.Om.isPot
  have hΦpsh : ∀ i, IsPsh S.A (Φ i) := fun _ => isPsh_of_isPosPot S.A _ S.Om.pos
  obtain ⟨hfin, hμ⟩ := maMeasure_thm S.A Φ hΦ hΦpsh
  set μ := maMeasure S.A Φ
  have hN : Continuous (secNorm S.L S.s) := continuous_secNorm S.A S.L S.s S.L_pot S.s_sec
  have hmeas : ∀ ε, Measurable (greenEp S.L S.s ε) := fun ε =>
    ((hN.measurable.pow_const 2).const_div ε |>.const_add 1).log

  have hlogN : Integrable (logNormSec S.L S.s) μ := by
    have hm : Measurable (logNormSec S.L S.s) := hN.measurable.log
    exact ((hμ _ hm).1).1 (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc Φ hΦ)
  have hh : Integrable (fun x => Real.log (secNorm S.L S.s x ^ 2 + 1)) μ := by
    have hc : Continuous fun x => Real.log (secNorm S.L S.s x ^ 2 + 1) :=
      ((hN.pow 2).add continuous_const).log fun x =>
        (by positivity : (0 : ℝ) < secNorm S.L S.s x ^ 2 + 1).ne'
    exact ((hμ _ hc.measurable).1).1 (mIntegrableCont S.A Φ hΦ _ hc)
  have hG1 : Integrable (greenEp S.L S.s 1) μ := by
    have : greenEp S.L S.s 1 = fun x =>
        Real.log (secNorm S.L S.s x ^ 2 + 1) - 2 * logNormSec S.L S.s x :=
      funext (greenEp_one_eq S.L S.s)
    rw [this]
    exact hh.sub (hlogN.const_mul 2)
  have hnorm : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x, ‖greenEp S.L S.s ε x‖ ≤ greenEp S.L S.s 1 x :=
    fun ε hε hε1 x => by
      rw [Real.norm_of_nonneg (greenEp_nonneg S.L S.s hε.le x)]
      exact greenEp_le_one S.L S.s hε.le hε1 x

  have hJ : ∀ ε, 0 < ε → ε ≤ 1 → ∀ t, S.J 0 ε t = ∫ x, greenEp S.L S.s ε x ∂μ := by
    intro ε hε hε1 t
    have hmix : mixedForms S.Om.pot (S.T t) 0 = Φ := by
      funext i
      simp [mixedForms, hΦdef]
    have hint : Integrable (greenEp S.L S.s ε) μ :=
      hG1.mono' (hmeas ε).aestronglyMeasurable (ae_of_all _ (hnorm ε hε hε1))
    have hmi : MIntegrable S.A Φ (greenEp S.L S.s ε) := ((hμ _ (hmeas ε)).1).2 hint
    show mInt S.A (mixedForms S.Om.pot (S.T t) 0) (greenEp S.L S.s ε) = _
    rw [hmix]
    exact (hμ _ (hmeas ε)).2 hmi

  have hT : Tendsto (fun ε => ∫ x, greenEp S.L S.s ε x ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε x => greenEp S.L S.s ε x) (f := fun _ => (0 : ℝ)) (greenEp S.L S.s 1)
      (Eventually.of_forall fun ε => (hmeas ε).aestronglyMeasurable)
      (eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε => ae_of_all _ (hnorm ε hε.1 hε.2))
      hG1 (ae_of_all _ fun x => greenEp_tendsto_zero S.L S.s x)
    simpa using this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ x, greenEp S.L S.s ε x ∂μ < η := (tendsto_order.1 hT).2 η hη
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min (u / 2) 1, lt_min (by linarith) one_pos, fun ε hε hεle t => ?_⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
  have hεu : ε < u := lt_of_le_of_lt (hεle.trans (min_le_left _ _)) (by linarith)
  rw [hJ ε hε hε1 t]
  exact (hsub ⟨hε, hεu⟩).le

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMassCharts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable locDens ChartPartition)

noncomputable section

namespace TailLogOfMass

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {Yo : Set X}
  {th : LocPot X} {u : Fin D → X → ℝ}

theorem potForm_contDiffAt (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (i : Fin D) (x : X) (k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart k).target) (hyYo : (A.chart k).symm y ∈ Yo)
    (hyU : (A.chart k).symm y ∈ th.U x) :
    ContDiffAt ℝ 2 ((potForm th (u i)).φ x ∘ (A.chart k).symm) y := by
  have h1 := ReciprocityTheory.AnForm.M.pot_contDiffAt_two hth x k hy hyU
  have ho : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' Yo) :=
    (A.chart k).isOpen_inter_preimage_symm hYo
  have h2 : ContDiffAt ℝ 2 (u i ∘ (A.chart k).symm) y :=
    ((hu i k).contDiffAt (ho.mem_nhds ⟨hy, hyYo⟩)).of_le (WithTop.coe_le_coe.2 le_top)
  exact h1.add h2

theorem locDens_nonneg_on (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (j : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart j).target) (hyYo : (A.chart j).symm y ∈ Yo) :
    0 ≤ locDens A (fun i => potForm th (u i)) j y :=
  ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y
      (potForm_contDiffAt hYo hth hu i _ j hy hyYo (th.mem_U _))
      (fun w => hnn i _ j y ⟨hy, hyYo, (potForm th (u i)).mem_U _⟩ w)

theorem locDens_chart_on (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (j k : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart j).target)
    (hyk : (A.chart j).symm y ∈ (A.chart k).source) (hyYo : (A.chart j).symm y ∈ Yo) :
    locDens A (fun i => potForm th (u i)) j y =
      locDens A (fun i => potForm th (u i)) k (A.chart k ((A.chart j).symm y)) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart k ∘ (A.chart j).symm) y).det := by
  set Φ : Fin D → LocPot X := fun i => potForm th (u i) with hΦ
  have hτ : AnalyticAt ℂ (A.chart k ∘ (A.chart j).symm) y := A.holo j k y ⟨hy, hyk⟩
  have hsk : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
    (A.chart k).left_inv hyk
  have htk : A.chart k ((A.chart j).symm y) ∈ (A.chart k).target := (A.chart k).map_source hyk
  have hL : locDens A Φ k (A.chart k ((A.chart j).symm y)) =
      ReciprocityTheory.AnForm.maDens (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
        (A.chart k ((A.chart j).symm y)) := by
    simp only [locDens, hsk]
  have hsm : ∀ i, ContDiffAt ℝ 2 (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
      ((A.chart k ∘ (A.chart j).symm) y) := fun i =>
    potForm_contDiffAt hYo hth hu i _ k htk
      (show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ Yo by rw [hsk]; exact hyYo)
      (show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ th.U ((A.chart j).symm y) by
        rw [hsk]; exact th.mem_U _)
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp
    (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
    (A.chart k ∘ (A.chart j).symm) y hτ hsm
  have key : locDens A Φ j y = ReciprocityTheory.AnForm.maDens (fun i =>
      (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y')) ∘
        (A.chart k ∘ (A.chart j).symm)) y := by
    unfold locDens
    apply ReciprocityTheory.AnForm.M.maDens_congr_hessC
    intro i
    apply ReciprocityTheory.AnForm.M.hessCGerm
    have hWo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
    filter_upwards [hWo.mem_nhds (show y ∈ (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (A.chart k).source from ⟨hy, hyk⟩)] with w hw
    simp only [Function.comp_apply]
    rw [(A.chart k).left_inv hw.2]
  rw [hL, key]
  exact hcomp

theorem weight_nonneg (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (P : ChartPartition A) (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x) (hoff : ∀ x, x ∉ Yo → h x = 0)
    (i : Fin A.n) {z : Fin D → ℂ} (hz : z ∈ (A.chart i).target) :
    0 ≤ P.χ i ((A.chart i).symm z) * h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z := by
  by_cases hzY : (A.chart i).symm z ∈ Yo
  · exact mul_nonneg (mul_nonneg (P.nonneg i _) (h0 _)) (locDens_nonneg_on hYo hth hu hnn i hz hzY)
  · rw [hoff _ hzY]; simp

theorem lintegral_target_le (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (P : ChartPartition A) (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x) (hoff : ∀ x, x ∉ Yo → h x = 0)
    (j : Fin A.n) (hm : AEMeasurable (fun y => h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)
      (volume.restrict (A.chart j).target)) :
    ∫⁻ y in (A.chart j).target, ENNReal.ofReal (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) ≤
      ∑ i, ∫⁻ z in (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
        h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hχ : ∀ i, ContinuousOn (fun y => P.χ i ((A.chart j).symm y)) (A.chart j).target := by
    intro i
    have := (P.smooth i j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hsplit : ∀ y ∈ (A.chart j).target,
      ENNReal.ofReal (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y) =
        ∑ i, ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
          (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)) := by
    intro y hy
    by_cases hyY : (A.chart j).symm y ∈ Yo
    · have ha : 0 ≤ h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y :=
        mul_nonneg (h0 _) (locDens_nonneg_on hYo hth hu hnn j hy hyY)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (P.nonneg i _) ha),
        ← Finset.sum_mul, P.sum_eq_one, one_mul]
    · simp [hoff _ hyY]
  rw [setLIntegral_congr_fun hT hsplit, lintegral_finsetSum' (f := fun i y => ENNReal.ofReal
    (P.χ i ((A.chart j).symm y) * (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))) _ (fun i _ =>
    ENNReal.measurable_ofReal.comp_aemeasurable (((hχ i).aemeasurable hT).mul hm))]
  refine Finset.sum_le_sum fun i _ => ?_
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart i).open_source
  have hτ : AnalyticOnNhd ℂ (A.chart i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) := A.holo j i
  have hinj : Set.InjOn (A.chart i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) := by
    intro a ha b hb hab
    exact (A.chart j).symm.injOn ha.1 hb.1 ((A.chart i).injOn ha.2 hb.2 hab)
  have himg : (A.chart i ∘ (A.chart j).symm) ''
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source) ⊆ (A.chart i).target := by
    rintro _ ⟨z, hz, rfl⟩; exact (A.chart i).map_source hz.2
  calc ∫⁻ y in (A.chart j).target, ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
          (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))
        = ∫⁻ y in (A.chart j).target,
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source).indicator
            (fun y => ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))) y := by
          refine setLIntegral_congr_fun hT fun y hy => ?_
          by_cases hyU : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source
          · rw [indicator_of_mem hyU]
          · rw [indicator_of_notMem hyU]
            have h1 : (A.chart j).symm y ∉ (A.chart i).source := fun h' => hyU ⟨hy, h'⟩
            have h2 : (A.chart j).symm y ∉ tsupport (P.χ i) := fun h' =>
              h1 (P.tsupport_subset i h')
            simp [image_eq_zero_of_notMem_tsupport h2]
      _ ≤ ∫⁻ y, ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source).indicator
            (fun y => ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y))) y := setLIntegral_le_lintegral _ _
      _ = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source,
            ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)) := lintegral_indicator hU.measurableSet _
      _ = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source,
            ENNReal.ofReal (Complex.normSq
              (ReciprocityTheory.AnForm.A.jacC (A.chart i ∘ (A.chart j).symm) y).det) *
            (fun z => ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
              h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z)) ((A.chart i ∘ (A.chart j).symm) y) := by
          refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
          have hs : (A.chart i).symm (A.chart i ((A.chart j).symm y)) = (A.chart j).symm y :=
            (A.chart i).left_inv hy.2
          show ENNReal.ofReal (P.χ i ((A.chart j).symm y) *
              (h ((A.chart j).symm y) * locDens A (fun i => potForm th (u i)) j y)) =
            ENNReal.ofReal (Complex.normSq
              (ReciprocityTheory.AnForm.A.jacC (A.chart i ∘ (A.chart j).symm) y).det) *
            ENNReal.ofReal (P.χ i ((A.chart i).symm (A.chart i ((A.chart j).symm y))) *
              h ((A.chart i).symm (A.chart i ((A.chart j).symm y))) *
              locDens A (fun i => potForm th (u i)) i (A.chart i ((A.chart j).symm y)))
          rw [hs, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
          by_cases hyY : (A.chart j).symm y ∈ Yo
          · rw [locDens_chart_on hYo hth hu j i hy.1 hy.2 hyY]
            congr 1
            ring
          · simp [hoff _ hyY]
      _ = ∫⁻ z in (A.chart i ∘ (A.chart j).symm) ''
            ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source),
            ENNReal.ofReal (P.χ i ((A.chart i).symm z) * h ((A.chart i).symm z) *
              locDens A (fun i => potForm th (u i)) i z) :=
          (ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul _ _ hU hτ hinj
            (fun z => ENNReal.ofReal (P.χ i ((A.chart i).symm z) * h ((A.chart i).symm z) *
              locDens A (fun i => potForm th (u i)) i z))).symm
      _ ≤ ∫⁻ z in (A.chart i).target, ENNReal.ofReal (P.χ i ((A.chart i).symm z) *
            h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) := lintegral_mono_set himg

theorem mInt_nonneg_of (hYo : IsOpen Yo) (hth : IsPotential A th)
    (hu : ∀ i, A.SmoothOn Yo (u i)) (hnn : ∀ i, FormNonneg A Yo (potForm th (u i)))
    (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x) (hoff : ∀ x, x ∉ Yo → h x = 0) :
    0 ≤ mInt A (fun i => potForm th (u i)) h := by
  unfold mInt
  split_ifs with hP
  · exact Finset.sum_nonneg fun i _ => setIntegral_nonneg (A.chart i).open_target.measurableSet
      fun z hz => weight_nonneg hYo hth hu hnn _ h h0 hoff i hz
  · exact le_rfl

theorem sum_lintegral_eq_mInt [CompactSpace X] [T2Space X] (hYo : IsOpen Yo)
    (hth : IsPotential A th) (hu : ∀ i, A.SmoothOn Yo (u i))
    (hnn : ∀ i, FormNonneg A Yo (potForm th (u i))) (h : X → ℝ) (h0 : ∀ x, 0 ≤ h x)
    (hoff : ∀ x, x ∉ Yo → h x = 0) (hI : MIntegrable A (fun i => potForm th (u i)) h) :
    ∑ i, ∫⁻ z in (A.chart i).target,
      ENNReal.ofReal ((ReciprocityTheory.AnForm.M.existsPartition A).some.χ i ((A.chart i).symm z) *
        h ((A.chart i).symm z) * locDens A (fun i => potForm th (u i)) i z) = ENNReal.ofReal (mInt A (fun i => potForm th (u i)) h) := by
  rw [mInt, dite_eq_left (ReciprocityTheory.AnForm.M.existsPartition A)]
  unfold ReciprocityTheory.AnForm.M.integralWith
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => setIntegral_nonneg
    (A.chart i).open_target.measurableSet fun z hz => weight_nonneg hYo hth hu hnn _ h h0 hoff i hz)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (ofReal_integral_eq_lintegral_ofReal
    (ReciprocityTheory.AnForm.M.integrableOn_weight A _ _ h hI i)
    (ae_restrict_of_forall_mem (A.chart i).open_target.measurableSet
      fun z hz => weight_nonneg hYo hth hu hnn _ h h0 hoff i hz)).symm

end TailLogOfMass

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

