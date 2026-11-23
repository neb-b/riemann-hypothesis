module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace BoundedPshData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)

def u (j : Fin B.N) : (Fin D → ℂ) → ℝ := B.chartFun B.ph j

def smoothed (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) : (Fin D → ℂ) → ℝ :=
  molli ρ t (B.u j)

def phReg (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) (x : X) : ℝ :=
  B.smoothed ρ t j (B.chart j x) - B.q j (B.chart j x)

def regularised (ρ : Mollifier D) (t ε : ℝ) (η : Fin B.N → X → ℝ) : X → ℝ :=
  B.glue (fun j x => B.phReg ρ t j x + 4 * ε * η j x) ε

end BoundedPshData

def BoundedChartComparison.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D), ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ j k : Fin B.N, ∀ x ∈ B.mid j ∩ B.mid k,
        |B.phReg ρ t j x - B.phReg ρ t k x| ≤ C / Real.log t⁻¹ + C * t

def BoundedGlue.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D) (η : Fin B.N → X → ℝ) (Cη t ε : ℝ),
    B.IsCutoffFamily η Cη → 0 < t → 0 < ε →
    (∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target) →
    (∀ j k, ∀ x ∈ B.mid j ∩ B.mid k, |B.phReg ρ t j x - B.phReg ρ t k x| ≤ ε) →
    A.Smooth (B.regularised ρ t ε η) ∧
      ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ w : Fin D → ℂ,
        -(4 * Cη * ε) * ‖w‖ ^ 2 ≤ levi (B.chartFun (B.regularised ρ t ε η) k) (B.chart k x) w

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PCutoffs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)

noncomputable section

theorem exists_smooth_bump_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K V : Set E} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧ (∀ y ∈ K, g y = 1) ∧
      IsCompact (tsupport g) ∧ tsupport g ⊆ V := by
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  have hd : Disjoint Wᶜ K := Set.disjoint_compl_left_iff_subset.2 hKW
  obtain ⟨f, hf, hrange, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, E)) (n := ⊤) hWo.isClosed_compl hK.isClosed hd
  have hsupp : tsupport f ⊆ closure W := by
    refine closure_mono fun y hy => ?_
    by_contra hyW
    exact hy ((h0 y).1 hyW)
  refine ⟨f, contMDiff_iff_contDiff.1 hf, fun y => hrange ⟨y, rfl⟩, fun y hy => (h1 y).1 hy,
    hWc.of_isClosed_subset (isClosed_tsupport f) hsupp, hsupp.trans hWV⟩

theorem levi_lower_bound_of_isCompact {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U K : Set (Fin D → ℂ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ w, -C * ‖w‖ ^ 2 ≤ levi f y w := by
  have hS : IsCompact (K ×ˢ sphere (0 : Fin D → ℂ) 1) := hK.prod (isCompact_sphere 0 1)
  have hc : ContinuousOn (fun p : (Fin D → ℂ) × (Fin D → ℂ) => levi f p.1 p.2)
      (K ×ˢ sphere (0 : Fin D → ℂ) 1) :=
    (ReciprocityTheory.AnForm.continuousOn_levi hU hf).mono (prod_mono hKU (subset_univ _))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun y hy w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi_zero]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hb := hC (y, ‖w‖⁻¹ • w) ⟨hy, by simpa using hu⟩
  have hb' : -max C 0 ≤ levi f y (‖w‖⁻¹ • w) := by
    have := (abs_le.1 (Real.norm_eq_abs _ ▸ hb)).1
    linarith [le_max_left C 0]
  have hw' : w = ‖w‖ • (‖w‖⁻¹ • w) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hw', ReciprocityTheory.AnForm.levi_smul_dir]
  have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hb' h2
  have hnn : ‖‖w‖ • (‖w‖⁻¹ • w)‖ = ‖w‖ := by rw [← hw']
  rw [hnn]
  linarith

theorem CutoffsExist.proof : CutoffsExist.Statement := by
  intro X _ _ _ D A P
  have hb : ∀ j, ∃ g : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧
      (∀ y ∈ P.chart j '' closure (P.inner j), g y = 1) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ P.chartMid j := by
    intro j
    have hcl : closure (P.inner j) ⊆ (P.chart j).source :=
      (P.closure_inner j).trans (P.mid_subset_source j)
    refine exists_smooth_bump_of_isCompact
      (isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hcl))
      ((P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
        (P.isOpen_mid j)) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(P.chart j).map_source (hcl hx), by
      rw [mem_preimage, (P.chart j).left_inv (hcl hx)]; exact P.closure_inner j hx⟩
  choose g hgs hg01 hg1 hgc hgt using hb
  have hgt' : ∀ j, tsupport (g j) ⊆ (P.chart j).target := fun j => (hgt j).trans inter_subset_left
  have hcp : ∀ j x, 0 ≤ chartPush (P.chart j) (g j) x ∧ chartPush (P.chart j) (g j) x ≤ 1 := by
    intro j x
    unfold chartPush
    by_cases hx : x ∈ (P.chart j).source
    · rw [indicator_of_mem hx]; exact hg01 j _
    · rw [indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hsm : ∀ j, A.Smooth (fun x => chartPush (P.chart j) (g j) x - 1) := by
    intro j a
    exact ContDiffOn.sub (f := chartPush (P.chart j) (g j) ∘ (A.chart a).symm)
      (smooth_chartPush (P.compat j) (hgs j) (hgc j) (hgt' j) a) contDiffOn_const
  have hC : ∀ j k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ P.chart k '' closure (P.mid k), ∀ w,
      -C * ‖w‖ ^ 2 ≤ levi ((fun x => chartPush (P.chart j) (g j) x - 1) ∘ (P.chart k).symm) y w := by
    intro j k
    have h := contDiffOn_compat (P.compat k) isOpen_univ (hsm j)
    rw [preimage_univ, inter_univ] at h
    refine levi_lower_bound_of_isCompact (P.chart k).open_target (h.of_le (WithTop.coe_le_coe.2 le_top))
      (isClosed_closure.isCompact.image_of_continuousOn
        ((P.chart k).continuousOn.mono (P.closure_mid k))) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (P.chart k).map_source (P.closure_mid k hx)
  choose C hC0 hC using hC
  refine ⟨fun j x => chartPush (P.chart j) (g j) x - 1, ∑ j, ∑ k, C j k, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j a
    exact (hsm j a).mono (inter_subset_inter_right _ (preimage_mono (subset_univ _)))
  · intro j x _
    constructor <;> linarith [hcp j x]
  · intro j x hx
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hx)
    have h1 : chartPush (P.chart j) (g j) x = 1 := by
      unfold chartPush
      rw [indicator_of_mem hs]
      exact hg1 j _ ⟨x, subset_closure hx, rfl⟩
    simp [h1]
  · intro j
    refine ⟨(P.chart j).symm '' tsupport (g j), (isCompact_symm_image (hgc j) (hgt' j)).isClosed,
      ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hgt j hy).2
    · intro x hx
      simp [chartPush_eq_zero (P.chart j) hx.2]
  · intro j k x hx w
    have h := hC j k (P.chart k x) ⟨x, subset_closure hx.2, rfl⟩ w
    have hle : C j k ≤ ∑ j, ∑ k, C j k :=
      (Finset.single_le_sum (fun k _ => hC0 j k) (Finset.mem_univ k)).trans
        (Finset.single_le_sum (f := fun j => ∑ k, C j k)
          (fun j _ => Finset.sum_nonneg fun k _ => hC0 j k) (Finset.mem_univ j))
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PKernelPositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Matrix

noncomputable section

namespace KernelPositive

def cquad {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  (fun k => (v k : ℂ)) ⬝ᵥ M *ᵥ fun k => (v k : ℂ)

theorem cquad_im {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) :
    (cquad v M).im = v ⬝ᵥ (M.map Complex.im *ᵥ v) := by
  simp [cquad, dotProduct, mulVec, Complex.im_sum, Complex.mul_im]

theorem intMat_mulVec_ofReal {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℝ)
    (h : B.map (Int.cast : ℤ → ℝ) *ᵥ v = 0) :
    B.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => (v k : ℂ)) = 0 := by
  funext k
  have hk := congrFun h k
  simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hk ⊢
  exact_mod_cast hk

theorem im_pos_of_punctured {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (h t).im) : 0 < (h 0).im := by
  by_contra hle
  rw [not_lt] at hle
  rcases hh.eventually_constant_or_nhds_le_map_nhds with hc | hmap
  · obtain ⟨t, ht, hte⟩ := (hpos.and (nhdsWithin_le_nhds hc)).exists
    rw [hte] at ht
    linarith
  · have hH : {w : ℂ | 0 < w.im ∨ w = h 0} ∈ 𝓝 (h 0) := by
      apply hmap
      rw [Filter.mem_map]
      filter_upwards [eventually_nhdsWithin_iff.mp hpos] with t ht
      by_cases h0 : t = 0
      · right
        rw [h0]
      · left
        exact ht h0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hH
    have hmem : h 0 - ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ ball (h 0) ε := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    rcases hball hmem with hw | hw
    · simp at hw
      linarith
    · have := congrArg Complex.im hw
      simp at this
      linarith

theorem pos_of_punctured {n a g : ℕ} (P : PeriodPolydisc n a g)
    {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT : P.IsTau0Ext T0) {v : Fin g → ℝ}
    (hv : v ≠ 0) (hB : ∀ i, (P.B i).map (Int.cast : ℤ → ℝ) *ᵥ v = 0) {z : Fin n → ℂ}
    (hz : z ∈ ball (0 : Fin n → ℂ) 1) (hz0 : ∀ k, z k ≠ 0) :
    0 < (cquad v (T0 z)).im := by
  have hzk : ∀ k, ‖z k‖ < 1 := fun k => (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.mp hz)
  have hw : logLift a z ∈ logCover P.a_le := by
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · have hi : (Fin.castLE P.a_le i).val < a := i.isLt
      simp only [logLift, if_pos hi, Complex.log_re]
      exact Real.log_neg (norm_pos_iff.mpr (hz0 _)) (hzk _)
    · simp only [logLift, if_neg (not_lt.mpr hk)]
      exact hzk k
  have hexp : expCover a (logLift a z) = z := by
    funext k
    by_cases hk : k.val < a
    · simp [expCover, logLift, hk, Complex.exp_log (hz0 k)]
    · simp [expCover, logLift, hk]
  have hT0 : T0 z = P.tau0 (logLift a z) := by
    rw [(hT.2 _ hw), hexp]
  have hsum : (∑ i : Fin a, (logLift a z (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
      (P.B i).map (Int.cast : ℤ → ℂ)) *ᵥ (fun k => (v k : ℂ)) = 0 := by
    refine Finset.sum_induction _ (fun N => N *ᵥ (fun k => (v k : ℂ)) = 0)
      (fun A B hA hB => by rw [add_mulVec, hA, hB, add_zero]) (zero_mulVec _) (fun i _ => ?_)
    rw [smul_mulVec, intMat_mulVec_ofReal _ _ (hB i), smul_zero]
  have hq : cquad v (T0 z) = cquad v (P.τ (logLift a z)) := by
    rw [hT0, cquad, cquad, PeriodPolydisc.tau0, sub_mulVec, hsum, sub_zero]
  rw [hq, cquad_im]
  simpa using (P.im_posDef _ hw).dotProduct_mulVec_pos hv

def line {n : ℕ} (z : Fin n → ℂ) (t : ℂ) : Fin n → ℂ := z + t • fun _ => (1 : ℂ)

theorem line_apply {n : ℕ} (z : Fin n → ℂ) (t : ℂ) (k : Fin n) : line z t k = z k + t := by
  simp [line]

end KernelPositive


open KernelPositive in
theorem kernelPositive_statement : KernelPositive.Statement := open KernelPositive in by
  intro n a g P T0 hT v hv hB z hz
  rw [← cquad_im]
  have hLa : AnalyticAt ℂ (line z) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hL0 : line z 0 = z := by simp [line]
  have hG : AnalyticAt ℂ (fun t => cquad v (T0 (line z t))) 0 := by
    have h : (fun t => cquad v (T0 (line z t))) =
        ∑ p, ∑ q, fun t => (v p : ℂ) * (T0 (line z t) p q * (v q : ℂ)) := by
      funext t
      simp [cquad, dotProduct, mulVec, Finset.sum_apply, Finset.mul_sum]
    rw [h]
    refine Finset.analyticAt_sum _ fun p _ => Finset.analyticAt_sum _ fun q _ => ?_
    exact analyticAt_const.mul
      ((AnalyticAt.comp_of_eq (hT.1 p q z hz) hLa hL0).mul analyticAt_const)
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), line z t ∈ ball (0 : Fin n → ℂ) 1 :=
    hLa.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hL0]; exact hz))
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ k, line z t k ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    by_cases hzk : z k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [line_apply, hzk, zero_add]
      exact ht
    · have hc : ContinuousAt (fun t : ℂ => z k + t) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have := hc.eventually_ne (by simpa using hzk)
      exact nhdsWithin_le_nhds (this.mono fun t ht => by rw [line_apply]; exact ht)
  have hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (cquad v (T0 (line z t))).im := by
    filter_upwards [nhdsWithin_le_nhds hball, hne] with t ht1 ht2
    exact pos_of_punctured P hT hv hB ht1 ht2
  have := im_pos_of_punctured hG hpos
  simpa only [hL0] using this

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StLogCoverDescent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def LogCoverDescent.Statement : Prop :=
  ∀ (n a : ℕ) (h : a ≤ n) (φ : (Fin n → ℂ) → ℂ), AnalyticOnNhd ℂ φ (logCover h) →
    (∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) →
    AnalyticOnNhd ℂ (fun z => φ (logLift a z)) (puncturedChart h (ball 0 1)) ∧
      ∀ w ∈ logCover h, φ (logLift a (expCover a w)) = φ w

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsChartBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (Mollifier)

noncomputable section

def ChartMollifiedBounds.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ)
    (A : ReciprocityTheory.AnForm.M.FinHolAtlas D X) (R : RegChartData A) (ρ : Mollifier D),
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      (∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target) ∧
      ∀ K : ℝ, 0 ≤ K → ∀ j : Fin R.N, ∀ x ∈ R.mid j,
        -K - C ≤ R.phReg ρ K t j x ∧ R.phReg ρ K t j x ≤ C ∧
          (x ∈ R.Yo → R.ph x ≤ R.phReg ρ K t j x)

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncPsh
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

def TruncPsh.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ B : ℝ, 0 < δ ∧ ∀ j : Fin R.N, ∃ V : Set (Fin D → ℂ), IsOpen V ∧
      V ⊆ (R.chart j).target ∧ (∀ x ∈ R.mid j, closedBall (R.chart j x) δ ⊆ V) ∧
      ∀ K : ℝ, IsPsh V (R.trunc K j) ∧ ∀ y ∈ V, R.trunc K j y ≤ max B (-K)

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncTransfer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

def TruncTransfer.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ L B : ℝ, 0 < δ ∧ 1 ≤ L ∧ ∀ (K : ℝ) (j k : Fin R.N),
      ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
        R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t

end

end GroundTheory.Heights₂.Heights.Regular
end

