module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable ChartPartition integralWith
  locDens chartPartMeasure integral_chartPartMeasure isFiniteMeasure_chartPartMeasure existsPartition
  locDensCont mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem tendsto_ell : Tendsto ell (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

section Signed

variable {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

def tvMeasure (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : Measure X :=
  ∑ j, (chartPartMeasure A (existsPartition A).some Φ 1 j +
    chartPartMeasure A (existsPartition A).some Φ (-1) j)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem chart_weight_continuousOn (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
  have h := (P.smooth j j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact continuousOn_const.mul (h.mul (locDensCont A Φ hΦ j))


omit [CompactSpace X] [T2Space X] in
theorem integrableOn_chart_of_part (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ)
    (hg : Measurable g) (hi : Integrable g (chartPartMeasure A P Φ s j)) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hwc := chart_weight_continuousOn A P Φ hΦ s j
  have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hd : AEMeasurable (fun y => ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hwc.aemeasurable hT)
  have hlt : ∀ᵐ y ∂(volume.restrict (A.chart j).target), ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hsymm' : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hfun : (fun y => (ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y))).toReal • (g ∘ (A.chart j).symm) y) = fun y => g ((A.chart j).symm y) *
        max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
    funext y
    rw [ENNReal.toReal_ofReal', smul_eq_mul, Function.comp_apply, mul_comm]
  unfold chartPartMeasure at hi
  rw [integrable_map_measure hg.aestronglyMeasurable hsymm',
    integrable_withDensity_iff_integrable_smul₀' hd hlt, hfun] at hi
  exact hi

theorem abs_mInt_le (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (f : X → ℝ) (hf : Measurable f) (hfi : MIntegrable A Φ f) :
    Integrable f (tvMeasure A Φ) ∧ |mInt A Φ f| ≤ ∫ x, |f x| ∂tvMeasure A Φ := by
  have h1 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ 1 j f hf hfi
  have h2 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ (-1) j f hf hfi
  have hI : ∀ j, Integrable f (chartPartMeasure A (existsPartition A).some Φ 1 j +
      chartPartMeasure A (existsPartition A).some Φ (-1) j) :=
    fun j => (h1 j).1.add_measure (h2 j).1
  have hm : mInt A Φ f = ∑ j, (∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ 1 j -
      ∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ (-1) j) := by
    rw [mInt, dite_eq_left (existsPartition A)]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(h1 j).2, (h2 j).2, ← integral_sub
      (integrableOn_chart_of_part A _ Φ hΦ 1 j f hf (h1 j).1)
      (integrableOn_chart_of_part A _ Φ hΦ (-1) j f hf (h2 j).1)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    ring
  refine ⟨integrable_finsetSum_measure.2 fun j _ => hI j, ?_⟩
  rw [hm, tvMeasure, integral_finsetSum_measure fun j _ => (hI j).abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [integral_add_measure (h1 j).1.abs (h2 j).1.abs]
  exact (abs_sub _ _).trans (add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs)

end Signed

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)

@[instance_reducible] def projectiveLineBorel : MeasurableSpace (OnePoint ℂ) := borel _

attribute [local instance] projectiveLineBorel

theorem projectiveLine_borelSpace : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

attribute [local instance] projectiveLine_borelSpace

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.IntegrableOnTargetOfMIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt MIntegrable integralWith locDens)

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem chartPartition_le_one {A : FinHolAtlas e X} (P : ChartPartition A) (j : Fin A.n) (x : X) :
    P.χ j x ≤ 1 := by
  rw [← P.sum_eq_one x]
  exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)

theorem integrableOn_target_of_mIntegrable [CompactSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (P : ChartPartition A) {g : X → ℝ} (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      (A.chart j).target := by
  have hsub := P.tsupport_subset j
  have hKc : IsCompact ((A.chart j) '' tsupport (P.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsub)
  have hKt : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsub hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h
    exact h
  have hKm : MeasurableSet ((A.chart j) '' tsupport (P.χ j)) := hKc.isClosed.measurableSet
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) ((A.chart j) '' tsupport (P.χ j)) :=
    Integrable.bdd_mul (c := 1) (hg j _ hKt hKc) ((hχc.mono hKt).aestronglyMeasurable hKm)
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun y _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
        exact chartPartition_le_one P j _))
  refine (h1.of_forall_sdiff_eq_zero hT fun y hy => ?_).congr_fun (fun y _ => by ring) hT
  have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h => hy.2 ⟨_, h, (A.chart j).right_inv hy.1⟩
  rw [image_eq_zero_of_notMem_tsupport this, zero_mul]

theorem mInt_le_mul_of_le [CompactSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (V : Set X)
    {f g : X → ℝ} {c : ℝ} (hg : MIntegrable A Φ g)
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V → 0 ≤ locDens A Φ j y)
    (hf0 : ∀ x, 0 ≤ f x) (hfV : ∀ x ∉ V, f x = 0) (hgV : ∀ x ∉ V, g x = 0)
    (hfg : ∀ x ∈ V, f x ≤ c * g x) : mInt A Φ f ≤ c * mInt A Φ g := by
  classical
  unfold mInt
  split_ifs with h
  · unfold integralWith
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← integral_const_mul]
    have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    refine integral_mono_of_nonneg ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
      ((integrableOn_target_of_mIntegrable A Φ h.some hg j).const_mul c)
      ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
    · by_cases hV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf0 _)) (hdens j y hy hV)
      · simp [hfV _ hV]
    · by_cases hV : (A.chart j).symm y ∈ V
      · calc h.some.χ j ((A.chart j).symm y) * f ((A.chart j).symm y) * locDens A Φ j y
            ≤ h.some.χ j ((A.chart j).symm y) * (c * g ((A.chart j).symm y)) * locDens A Φ j y :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfg _ hV) (h.some.nonneg j _))
                (hdens j y hy hV)
          _ = c * (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y) := by ring
      · simp [hfV _ hV, hgV _ hV]
  · simp

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

noncomputable section

theorem two_le_smooth_kb : (2 : WithTop ℕ∞) ≤ ∞ := by norm_cast

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_abs_le_local (A : FinHolAtlas D X) (θ om : LocPot X) (hθ : IsPotential A θ)
    (hom : IsPotential A om) (hpos : IsPosPot A om) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ M : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (θ.U p ∩ om.U p) ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin D → ℂ,
        |levi (θ.φ p ∘ (A.chart j).symm) y u| ≤ M * levi (om.φ p ∘ (A.chart j).symm) y u := by
  set c := A.chart j with hc
  set O := c.target ∩ c.symm ⁻¹' (θ.U p ∩ om.U p) with hO
  have hOo : IsOpen O := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    ((θ.isOpen_U p).inter (om.isOpen_U p))
  have hpO : c p ∈ O := ⟨c.map_source hp, by
    simp only [Set.mem_preimage, c.left_inv hp]; exact ⟨θ.mem_U p, om.mem_U p⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo _ hpO
  have hcb : Metric.closedBall (c p) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  have homs : ContDiffOn ℝ 2 (om.φ p ∘ c.symm) O :=
    ((hom.1 p j).mono fun y (hy : y ∈ O) => ⟨hy.1, hy.2.2⟩).of_le two_le_smooth_kb
  have hθs : ContDiffOn ℝ 2 (θ.φ p ∘ c.symm) O :=
    ((hθ.1 p j).mono fun y (hy : y ∈ O) => ⟨hy.1, hy.2.1⟩).of_le two_le_smooth_kb
  set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin D → ℂ) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : K ⊆ O ×ˢ Set.univ := Set.prod_mono hcb (Set.subset_univ _)
  have hpos' : ∀ q ∈ K, 0 < levi (om.φ p ∘ c.symm) q.1 q.2 := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    refine hpos p j y ⟨(hcb hy).1, (hcb hy).2.2⟩ u ?_
    rintro rfl
    simp at hu
  have hcont : ContinuousOn (fun q : (Fin D → ℂ) × (Fin D → ℂ) =>
      |levi (θ.φ p ∘ c.symm) q.1 q.2| / levi (om.φ p ∘ c.symm) q.1 q.2) K :=
    (((continuousOn_levi hOo hθs).mono hKO).abs).div ((continuousOn_levi hOo homs).mono hKO)
      (fun q hq => (hpos' q hq).ne')
  obtain ⟨M, hM⟩ := hKc.bddAbove_image hcont
  refine ⟨r / 2, by linarith, M, hcb, fun y hy u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [levi_zero]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨v, hv'⟩ : ∃ v : Fin D → ℂ, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
    have hv : v ∈ Metric.sphere (0 : Fin D → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hq : (y, v) ∈ K := ⟨hy, hv⟩
    have h1 : |levi (θ.φ p ∘ c.symm) y v| / levi (om.φ p ∘ c.symm) y v ≤ M :=
      hM ⟨(y, v), hq, rfl⟩
    have h2 := hpos' _ hq
    have h3 : |levi (θ.φ p ∘ c.symm) y v| ≤ M * levi (om.φ p ∘ c.symm) y v := by
      rwa [div_le_iff₀ h2] at h1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖ := ⟨_, rfl⟩
    have huv : u = s • v := by
      rw [hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [huv, levi_smul_dir, levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg s)]
    have : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith

theorem levi_abs_le_global (A : FinHolAtlas D X) (hX : IsCompact (Set.univ : Set X))
    (θ om : LocPot X) (hθ : IsPotential A θ) (hom : IsPotential A om) (hpos : IsPosPot A om) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (θ.U x ∩ om.U x),
      ∀ v : Fin D → ℂ,
        |levi (θ.φ x ∘ (A.chart k).symm) y v| ≤ M * levi (om.φ x ∘ (A.chart k).symm) y v := by
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p =>
    Classical.choose_spec (A.cover p)
  have key := fun p => levi_abs_le_local A θ om hθ hom hpos p (chartIdx A p) (hsrc p)
  choose r hr m hsub hbd using key
  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' Metric.ball (A.chart (chartIdx A p) p) (r p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := hX.elim_finite_subcover V hVo
    (fun p _ => Set.mem_iUnion.2 ⟨p, hsrc p, Set.mem_preimage.mpr (Metric.mem_ball_self (hr p))⟩)
  refine ⟨∑ p ∈ t, |m p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro x k y hy v
  set C := ∑ p ∈ t, |m p| with hC
  obtain ⟨hyk, hyU⟩ := hy
  have hqθ : (A.chart k).symm y ∈ θ.U x := hyU.1
  have hqom : (A.chart k).symm y ∈ om.U x := hyU.2
  set q := (A.chart k).symm y with hq
  obtain ⟨p, hpt, hqV⟩ : ∃ p ∈ t, q ∈ V p := by
    simpa using ht (Set.mem_univ q)
  set j := chartIdx A p with hj
  set c := A.chart j with hc
  have hqs : q ∈ c.source := hqV.1
  have hqb : c q ∈ Metric.ball (c p) (r p) := hqV.2
  have hcqO := hsub p (Metric.ball_subset_closedBall hqb)
  have hqp : q ∈ θ.U p ∩ om.U p := by
    have := hcqO.2; rwa [Set.mem_preimage, c.left_inv hqs] at this
  have hcqt : c q ∈ c.target := c.map_source hqs
  have hsc : c.symm (c q) = q := c.left_inv hqs
  set τ := c ∘ (A.chart k).symm with hτd
  have hτ : AnalyticAt ℂ τ y := A.holo k j y ⟨hyk, hqs⟩
  have hτy : τ y = c q := rfl
  have hsrcev : ∀ᶠ y' in 𝓝 y, (A.chart k).symm y' ∈ c.source :=
    ((A.chart k).continuousAt_symm hyk).preimage_mem_nhds (c.open_source.mem_nhds hqs)
  have hgerm : ∀ f : X → ℝ, f ∘ (A.chart k).symm =ᶠ[𝓝 y] (f ∘ c.symm) ∘ τ := fun f => by
    filter_upwards [hsrcev] with y' hy'
    simp only [Function.comp_apply, τ, c.left_inv hy']
  have hsm : ∀ P : LocPot X, IsPotential A P → ∀ z, q ∈ P.U z →
      ContDiffAt ℝ 2 (P.φ z ∘ c.symm) (c q) := by
    intro P hP z hz
    have hOz : IsOpen (c.target ∩ c.symm ⁻¹' P.U z) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target (P.isOpen_U z)
    exact ((hP.1 z j).of_le two_le_smooth_kb).contDiffAt
      (hOz.mem_nhds ⟨hcqt, by simp only [Set.mem_preimage, hsc]; exact hz⟩)
  have hbase : ∀ P : LocPot X, IsPotential A P → q ∈ P.U x → q ∈ P.U p → ∀ u : Fin D → ℂ,
      levi (P.φ x ∘ c.symm) (c q) u = levi (P.φ p ∘ c.symm) (c q) u := by
    intro P hP hx hp u
    obtain ⟨W, hWo, hqW, G, hG, hGeq⟩ := hP.2 x p q ⟨hx, hp⟩
    have hGa : AnalyticAt ℂ (G ∘ c.symm) (c q) :=
      hG j (c q) ⟨hcqt, by show c.symm (c q) ∈ W; rw [hsc]; exact hqW⟩
    have hRe : ContDiffAt ℝ 2 (fun z => ((G ∘ c.symm) z).re) (c q) := by
      have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp (c q)
        (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
      simpa [Function.comp_def] using this
    have hev : P.φ x ∘ c.symm =ᶠ[𝓝 (c q)]
        fun z => (P.φ p ∘ c.symm) z + 1 * ((G ∘ c.symm) z).re := by
      have hopen : IsOpen (W ∩ P.U x ∩ P.U p) :=
        (hWo.inter (P.isOpen_U x)).inter (P.isOpen_U p)
      have : ∀ᶠ z in 𝓝 (c q), c.symm z ∈ W ∩ P.U x ∩ P.U p :=
        (c.continuousAt_symm hcqt).preimage_mem_nhds
          (hopen.mem_nhds (by rw [hsc]; exact ⟨⟨hqW, hx⟩, hp⟩))
      filter_upwards [this] with z hz
      have := hGeq (c.symm z) hz
      simp only [Function.comp_apply, one_mul]
      linarith
    rw [levi_congr hev, levi_add_smul 1 (hsm P hP p hp) hRe, levi_re_analytic hGa]
    ring
  have htr : ∀ P : LocPot X, IsPotential A P → q ∈ P.U x → q ∈ P.U p →
      levi (P.φ x ∘ (A.chart k).symm) y v = levi (P.φ p ∘ c.symm) (c q) (fderiv ℂ τ y v) := by
    intro P hP hx hp
    rw [levi_congr (hgerm _), levi_comp v hτ (by rw [hτy]; exact hsm P hP x hx), hτy,
      hbase P hP hx hp]
  have hb := hbd p (c q) (Metric.ball_subset_closedBall hqb) (fderiv ℂ τ y v)
  have hLom : 0 ≤ levi (om.φ p ∘ c.symm) (c q) (fderiv ℂ τ y v) := by
    rcases eq_or_ne (fderiv ℂ τ y v) 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (hpos p j (c q) ⟨hcqt, hcqO.2.2⟩ _ h0).le
  have hCm : m p ≤ C :=
    (le_abs_self (m p)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hpt)
  rw [htr θ hθ hqθ hqp.1, htr om hom hqom hqp.2]
  nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StBoundingKaehler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def BoundingKaehler.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (_ : KaehlerForm A) (m : ℕ) (th : Fin m → LocPot X), (∀ i, IsPotential A (th i)) →
    ∃ Om : KaehlerForm A, ∀ i,
      LeviLe A Set.univ 1 (th i) 1 Om.pot ∧ LeviLe A Set.univ (-1) Om.pot 1 (th i)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

def secOpen (s : X → X → ℂ) : Set X := {y | s y y ≠ 0}

def rSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ := Real.exp 1 - 2 * logNormSec L s y

structure IsLemmaEPot (A : FinHolAtlas D X) (Om : KaehlerForm A) (L : LocPot X)
    (s : X → X → ℂ) (C₁ : ℝ) (u : X → ℝ) : Prop where
  smooth : A.SmoothOn (secOpen s) u
  nonneg : FormNonneg A (secOpen s) (potForm Om.pot u)
  nonpos : ∀ x ∈ secOpen s, u x ≤ 0
  le_u : ∀ x ∈ secOpen s, -(C₁ * Real.log (rSec L s x)) ≤ u x
  smooth_or_pole : A.Smooth u ∨ ∀ y, y ∉ secOpen s → Tendsto u (𝓝[secOpen s] y) atBot

def LemmaETailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailLogBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

section Inhabitants

open OnePoint
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isPlurisubharmonic projLine_isHolomorphicSection crd0 crd1 fsPot_φ_coe
  projLineSection_infty projLineSection_coe)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def ListMono.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A) (C₁ : ℝ) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsBoundedPotForm A Yo r Om C₁ (th i) (u i)) →
    (∀ i, FormNonneg A Yo (potForm Om.pot (u i))) ∧
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y) ∧
    ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (∀ x, x ∉ Yo → g x = 0) →
      MIntegrable A (fun i => potForm Om.pot (u i)) g →
      MIntegrable A (fun i => potForm (th i) (u i)) g ∧
        mInt A (fun i => potForm (th i) (u i)) g ≤ mInt A (fun i => potForm Om.pot (u i)) g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

