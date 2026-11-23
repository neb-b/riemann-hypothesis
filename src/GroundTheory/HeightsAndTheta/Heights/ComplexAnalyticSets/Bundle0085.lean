module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchIntDecompose
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem BranchIntDecompose.proof (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hGen : ComplexSets.GenericProjectionFinite.Statement) (hSum : ChartIntSumOffHyperplane.Statement)
    (hBr : BranchChartInt.Statement) : BranchIntDecompose.Statement := by
  intro n d J u q m γ ord hJ hdim hu hcov hdisj _
  obtain ⟨N₀, hN₀, hcovN⟩ := hcov
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu ⟨N₀, hN₀, hcovN⟩ hdisj b 0
      (Metric.mem_ball_self (γ b).radius_pos) (γ b).map_zero _
      (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨N₀ ∩ ⋂ b, Metric.ball q (e b),
    inter_mem hN₀ (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)),
    fun f ψ hf _ hfN hψ => ?_⟩
  have hex : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A :=
    (hGen n (d + 1) J hJ hdim).2.1
  have hAf : IsFiniteProjection J hex.choose := hex.choose_spec
  have hvar : varInt J (d + 1) f ψ = chartInt J hex.choose f ψ := by
    rw [varInt, dite_eq_left hex]
  have hbr : ∀ b, Integrable (chartDens J hex.choose ((γ b).image.indicator f) ψ) ∧
      chartInt J hex.choose ((γ b).image.indicator f) ψ =
        ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
          (Metric.ball 0 (γ b).radius) := by
    intro b
    refine hBr n (d + 1) J hex.choose q (γ b) f ψ hJ hdim hAf hf.continuous hψ
      ⟨Metric.closedBall 0 ((γ b).radius / 2), isCompact_closedBall _ _,
        Metric.closedBall_subset_ball (half_lt_self (γ b).radius_pos), fun t ht htK => ?_⟩
    by_contra hne
    have hx := hfN (subset_tsupport f hne)
    exact htK (Metric.ball_subset_closedBall (hpe b t ht (Set.mem_iInter.1 hx.2 b)))
  have hpt : ∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, (γ b).image.indicator f x := by
    intro x hxZ hux
    by_cases hfx : f x = 0
    · rw [hfx]
      exact (Finset.sum_eq_zero fun b _ => by by_cases hb : x ∈ (γ b).image <;> simp [hb, hfx]).symm
    · have hxN := hfN (subset_tsupport f hfx)
      obtain ⟨b₀, hb₀⟩ := Set.mem_iUnion.1 (hcovN ⟨hxZ, hxN.1⟩)
      rw [Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun hxb => hux (hdisj b b₀ hb ⟨hxb, hb₀⟩)) _)
        (fun h => absurd (Finset.mem_univ b₀) h), Set.indicator_of_mem hb₀]
  rw [hvar, hSum n (d + 1) J hex.choose u m f (fun b => (γ b).image.indicator f) ψ hJ hdim hAf hu hpt
    (fun b => (hbr b).1)]
  exact Finset.sum_congr rfl fun b _ => (hbr b).2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntCountAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartIntCountAdd

variable {n d : ℕ}

theorem hasSum_indicator {E : ℕ → Set (Fin n → ℂ)} (hE : Pairwise (Function.onFun Disjoint E))
    (g : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    HasSum (fun i => (E i).indicator g x) ((⋃ i, E i).indicator g x) := by
  by_cases hx : x ∈ ⋃ i, E i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have hval : (⋃ i, E i).indicator g x = (E j).indicator g x := by
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hj]
    rw [hval]
    refine hasSum_single j fun i hi => ?_
    have hxi : x ∉ E i := fun hxi => Set.disjoint_left.1 (hE hi) hxi hj
    simp [hxi]
  · have h0 : ∀ i, (E i).indicator g x = 0 := fun i => by
      have hxi : x ∉ E i := fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩)
      simp [hxi]
    have hu : (⋃ i, E i).indicator g x = 0 := by simp only [Set.indicator_of_notMem hx]
    simp only [h0, hu]
    exact hasSum_zero


open Classical in
theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, (if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0) := by
  unfold sheetSum
  exact finsum_mem_eq_finite_toFinset_sum _ hfin

theorem hasSum_sheetSum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : ℕ → (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (hF : ∀ x s, HasSum (fun i => F i x s) (G x s)) :
    HasSum (fun i => sheetSum J A (F i) y) (sheetSum J A G y) := by
  classical
  simp only [sheetSum_eq_sum hfin]
  refine hasSum_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hF x _
  · simp only [dif_neg h]; exact hasSum_zero

theorem abs_sheetSum_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    |sheetSum J A F y| ≤ sheetSum J A (fun x s => |F x s|) y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h, le_refl]
  · simp only [dif_neg h, abs_zero, le_refl]

theorem sheetSum_mono {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ}
    (hFG : ∀ x s, F x s ≤ G x s) : sheetSum J A F y ≤ sheetSum J A G y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hFG x _
  · simp only [dif_neg h, le_refl]

theorem indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    S.indicator f x * c = S.indicator (fun z => f z * c) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| = S.indicator (fun z => |f z * c|) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul_le (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| ≤ |f x * c| := by
  by_cases hx : x ∈ S <;> simp [hx] <;> positivity

end ChartIntCountAdd


open ChartIntCountAdd in
theorem ChartIntCountAdd.proof (hCM : ChartMassCompact.Statement) : ChartIntCountAdd.Statement := by
  intro n d W A f φ E hW hdim hA hf hfc hφ hEm hE
  have hfin : ∀ y, (fibre W A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
  have hmeas : ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
      Measurable (chartDens W A g φ) ∧ Measurable (chartAbsDens W A g φ) := fun g hg =>
    SheetSumMeasurable.proof n d W A g φ hW hdim hA hg hφ
  have hgm : ∀ i, Measurable ((E i).indicator f) := fun i => hf.measurable.indicator (hEm i)
  have hgu : Measurable ((⋃ i, E i).indicator f) := hf.measurable.indicator (MeasurableSet.iUnion hEm)

  have hdens : ∀ y, HasSum (fun i => chartDens W A ((E i).indicator f) φ y)
      (chartDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [indicator_mul]
    exact hasSum_indicator hE _ x
  have habs : ∀ y, HasSum (fun i => chartAbsDens W A ((E i).indicator f) φ y)
      (chartAbsDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartAbsDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [abs_indicator_mul]
    exact hasSum_indicator hE _ x

  have hdom : Integrable (chartAbsDens W A ((⋃ i, E i).indicator f) φ) := by
    refine (hCM n d W A f φ hW hdim hA hf.continuousOn hφ (Or.inl hfc)).mono'
      (hmeas _ hgu).2.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartAbsDens
    refine (abs_sheetSum_le (hfin y) _).trans (sheetSum_mono (hfin y) fun x s => ?_)
    rw [abs_abs]
    exact abs_indicator_mul_le _ _ _ _
  have hsum : (fun y => ∑' i, chartAbsDens W A ((E i).indicator f) φ y) =
      chartAbsDens W A ((⋃ i, E i).indicator f) φ := funext fun y => (habs y).tsum_eq
  exact hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun i => chartDens W A ((E i).indicator f) φ)
    (f := chartDens W A ((⋃ i, E i).indicator f) φ)
    (fun i => chartAbsDens W A ((E i).indicator f) φ)
    (fun i => (hmeas _ (hgm i)).1.aestronglyMeasurable)
    (fun i => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact abs_sheetSum_le (hfin y) _)
    (ae_of_all _ fun y => (habs y).summable)
    (by rw [hsum]; exact hdom)
    (ae_of_all _ hdens)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal

noncomputable section

namespace ChartMassCompact

variable {n d : ℕ}

theorem mdisc_coord_zero {D : ℕ} (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (hi : M i = 0) : ReciprocityTheory.AnForm.mdisc M = 0 := by
  rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨j, hj⟩ := hr i
    refine mul_eq_zero_of_right _ (Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_)
    simp [hj, hi]
  · rw [ReciprocityTheory.AnForm.A.polCoef_eq_zero r hr, zero_mul]

theorem hessC_eq_zero_of_eventuallyEq {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] 0) : ReciprocityTheory.AnForm.hessC φ z = 0 := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ (0 : (Fin D → ℂ) → ℝ) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ φ) z = 0 := by
    rw [h1.fderiv_eq]
    simp
  ext i j
  simp [ReciprocityTheory.AnForm.hessC, h2]

theorem maDens_eq_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (i : Fin d) (hx : x ∉ tsupport (ψ i)) :
    ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
  obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs
  have hcont : ContinuousAt s (A *ᵥ x) := (hsd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hev : (ψ i ∘ s) =ᶠ[𝓝 (A *ᵥ x)] 0 := by
    have hnhds : (tsupport (ψ i))ᶜ ∈ 𝓝 (s (A *ᵥ x)) := by
      rw [hsx]
      exact (isClosed_tsupport _).isOpen_compl.mem_nhds hx
    filter_upwards [hcont.preimage_mem_nhds hnhds] with y hy
    show ψ i (s y) = 0
    exact image_eq_zero_of_notMem_tsupport hy
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_coord_zero _ i (hessC_eq_zero_of_eventuallyEq hev)]
  simp

theorem integrable_ball (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (ψ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (hψ : ∀ k, SmoothNear (zeroSet J) (ψ k)) (R : ℝ) :
    Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ) := by
  obtain ⟨K, hK, hle⟩ := hC n d J A ψ R hJ hd hA hψ
  have hmeas := (SheetSumMeasurable.proof n d J A
    ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ hJ hd hA
    (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbd : Bornology.IsBounded
      (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
    (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
  obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
  have h1 := hle (fun _ => 1) measurable_const
  simp only [enorm_one, setLIntegral_one] at h1
  refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
  exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hMF n d J hJ hd R')

theorem chartAbsDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {K B : Set (Fin n → ℂ)} {M : ℝ}
    (hKB : K ⊆ B) (hM : ∀ x ∈ zeroSet J ∩ K, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hvan : ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0)
    (y : Fin d → ℂ) (hfin : (fibre J A y).Finite) :
    chartAbsDens J A f ψ y ≤ M * chartAbsDens J A (B.indicator fun _ => 1) ψ y := by
  classical
  unfold chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  split_ifs with h
  · dsimp only
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem (hKB hxK), one_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM x ⟨hxZ, hxK⟩) (abs_nonneg _)
    · rw [hvan x _ h.choose_spec hxK, abs_zero]
      positivity
  · simp

end ChartMassCompact


open ChartMassCompact in
theorem ChartMassCompact.proof (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement) :
    ChartMassCompact.Statement := by
  classical
  intro n d J A f ψ hJ hd hA hf hψ hsupp
  obtain ⟨K, hKc, hvan⟩ : ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
    rcases hsupp with hc | ⟨i, hc⟩
    · exact ⟨tsupport f, hc, fun x s _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩
    · exact ⟨tsupport (ψ i), hc, fun x s hs hx => by rw [maDens_eq_zero hs ψ i hx, mul_zero]⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKc.isBounded
  obtain ⟨M, hM⟩ := (hKc.inter_left (SheetSumMeasurable.isClosed_zeroSet J)).exists_bound_of_continuousOn
    (hf.mono Set.inter_subset_left)
  have heq : chartAbsDens J A f ψ = chartAbsDens J A ((zeroSet J).piecewise f 0) ψ := by
    funext y
    unfold chartAbsDens sheetSum
    refine finsum_congr fun x => finsum_congr fun hx => ?_
    simp only [Set.piecewise_eq_of_mem _ _ _ hx.1]
  have hgm : Measurable ((zeroSet J).piecewise f 0) :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : AEStronglyMeasurable (chartAbsDens J A f ψ) volume := by
    rw [heq]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hd hA hgm hψ).2.aestronglyMeasurable
  refine ((integrable_ball hC hMF J A ψ hJ hd hA hψ R).const_mul (max M 0)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  exact chartAbsDens_le J A f ψ hR (fun x hx => (Real.norm_eq_abs (f x) ▸ hM x hx).trans (le_max_left _ _))
    (le_max_right _ _) hvan y (FibreBound.proof n d J A hJ hd hA y).2.1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeChartGram
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

noncomputable section

theorem le_of_ringKrullDim_quotient {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

theorem coneBall_hausdorff_lt_top (hMF : MassFinite.Statement) {n e : ℕ} (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} < ⊤ := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  let P : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 h.matᵀ)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (h.matᵀ)⁻¹)
  have hsub : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} ⊆
      Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) := by
    rintro z ⟨hz, hzJ⟩
    refine ⟨P z, ⟨fun q hq => hzJ q hq, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff]
      calc ‖P z‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm z
        _ ≤ ‖P‖ * 1 := by gcongr
        _ < ‖P‖ + 1 := by linarith
    · ext i
      simp [P, Q, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
  have hd : (0 : ℝ) ≤ ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  calc _ ≤ Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1))) :=
        measure_mono hsub
    _ ≤ (‖Q‖₊ : ENNReal) ^ ((2 * (e + 1) : ℕ) : ℝ) *
          Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) :=
        Q.lipschitz.hausdorffMeasure_image_le hd _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top)
        (hMF n (e + 1) J hJ (by exact_mod_cast hdim) _)

theorem integral_line_gram {n : ℕ} (e : ℕ) (h : HermNorm n) (g : (Fin n → ℂ) → ℝ)
    (hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z))
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (g x * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1)))) := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMx : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hinv, h0, Matrix.mulVec_zero]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρx : h.dualNorm x = ρ := by
    rw [hρ_def, EuclideanSpace.norm_eq]
    rfl
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    exact hMx (by simpa using congrArg WithLp.ofLp h0)
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => g (h.pointOf z)) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (g x * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  rw [integral_congr_ae hae, integral_const_mul,
    integral_indicator_ball_norm_pow e (by positivity), hρx]
  rw [one_div, inv_pow, Nat.factorial_succ]
  have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PEnergyDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem EnergyDensNonneg.proof : EnergyDensNonneg.Statement := by
  intro n d s y v hs
  have hV : IsOpen {z | AnalyticAt ℂ s z} := isOpen_analyticAt ℂ s
  have hC : ∀ z ∈ {z | AnalyticAt ℂ s z}, ContDiffAt ℝ 2 (euclPot ∘ s) z := fun z hz =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm d (fun _ => euclPot ∘ s) v _ hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y hs
  intro _ z hz ξ
  rw [levi_comp ξ hz ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    TubeFormComparison.levi_euclPot]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end

end GroundTheory.Heights₂.Heights
end

