module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffHypInclAt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffMulOfTsupport
section
namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff Manifold

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem slice_mInt {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
    {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
    (B : FinHolAtlas e W) (hB : HoloMap B A Subtype.val) (Φ : Fin e → LocPot X)
    (hΦ : ∀ k, IsPotential A (Φ k)) (hψ : IsCompatChart A ψ)
    (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) (x : X) {V : Set X}
    (hV : IsOpen V) (hVψ : V ⊆ ψ.source) (hVΦ : ∀ k, V ⊆ (Φ k).U x)
    (hxW : x ∉ W → V ∩ W = ∅) {v : X → ℝ} (hv : A.Smooth v) (hvV : tsupport v ⊆ V) :
    mInt B (fun k => (Φ k).pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) =
      ∫ z, chartExt ψ v (hypInclAt i z) * densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) z := by
  by_cases hx : x ∈ W
  · have hne : Nonempty (ChartPartition B) := existsPartition B
    unfold mInt
    rw [dif_pos hne]
    unfold integralWith
    have hj := fun j => slice_chart B hB Φ hΦ hψ hWψ x hx hV hVψ hVΦ hv hvV hne.some j
    rw [Finset.sum_congr rfl (fun j _ => (hj j).2)]
    rw [← integral_finsetSum _ (fun j _ => (hj j).1)]
    congr 1
    funext z
    by_cases ht : hypInclAt i z ∈ ψ.target
    · simp only [Set.indicator_of_mem (show z ∈ hypInclAt i ⁻¹' ψ.target from ht)]
      obtain ⟨hpW, -, -⟩ := symm_hyp_mem hWψ ht
      rw [chartExt, Set.indicator_of_mem ht]
      simp only [sliceF, ← Finset.sum_mul]
      have h1 : ∑ j, extW W (hne.some.χ j) (ψ.symm (hypInclAt i z)) = 1 := by
        simp only [extW, hpW, dif_pos]
        exact hne.some.sum_eq_one _
      rw [h1, one_mul]
      rfl
    · simp only [Set.indicator_of_notMem (show z ∉ hypInclAt i ⁻¹' ψ.target from ht),
        Finset.sum_const_zero, chartExt, Set.indicator_of_notMem ht, zero_mul]
  · have hV0 := hxW hx
    have hv0 : ∀ p ∈ W, v p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport fun h => by
      have : p ∈ V ∩ W := ⟨hvV h, hp⟩
      rw [hV0] at this; exact this
    rw [mInt_zero_fun _ _ (g := v ∘ Subtype.val) (fun q : W => hv0 q q.2)]
    symm
    have : (fun z => chartExt ψ v (hypInclAt i z) * densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) z) =
        fun _ => 0 := by
      funext z
      by_cases ht : hypInclAt i z ∈ ψ.target
      · obtain ⟨hpW, -, -⟩ := symm_hyp_mem hWψ ht
        simp [chartExt, Set.indicator_of_mem ht, hv0 _ hpW]
      · simp [chartExt, Set.indicator_of_notMem ht]
    rw [this, integral_zero]

section Helpers

omit [T2Space X] [CompactSpace X]

theorem analyticAt_compat_fun {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : Fin e → ℂ}
    (hy : y ∈ ψ.target) (hyU : ψ.symm y ∈ U) : AnalyticAt ℂ (g ∘ ψ.symm) y := by
  obtain ⟨j, hj⟩ : ∃ j, ψ.symm y ∈ (A.chart j).source := A.cover (ψ.symm y)
  have h1 : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) y := (hψ j).2 y ⟨hy, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) y) :=
    hg j _ ⟨(A.chart j).map_source hj, by simpa [Function.comp, (A.chart j).left_inv hj] using hyU⟩
  refine (h2.comp h1).congr ?_
  filter_upwards [ψ.continuousAt_symm hy ((A.chart j).open_source.mem_nhds hj)] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem exists_cutoff {n : ℕ} {K U : Set (Fin n → ℂ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ ρ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ ρ ∧ IsCompact (tsupport ρ) ∧ tsupport ρ ⊆ U ∧
      ∃ O, IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ρ y = 1 := by
  have key : ∀ x, ∃ f : (Fin n → ℂ) → ℝ, tsupport f ⊆ U ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧
      (∀ y, 0 ≤ f y) ∧ (x ∈ K → f x = 1) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x (hKU hx)
      let b : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩
      refine ⟨b, ?_, b.hasCompactSupport, b.contDiff, fun y => b.nonneg, fun _ => ?_⟩
      · rw [b.tsupport_eq]
        exact (Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hrU
      · exact b.one_of_mem_closedBall (Metric.mem_closedBall_self (by show (0:ℝ) ≤ r / 4; linarith))
    · refine ⟨0, by simp, HasCompactSupport.zero, contDiff_const, fun _ => le_rfl, fun h => (hx h).elim⟩
  choose f hfU hfc hfd hf0 hf1 using key
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | 1 / 2 < f x y}) (fun x hx =>
    (isOpen_lt continuous_const (hfd x).continuous).mem_nhds (by
      show (1 : ℝ) / 2 < f x x
      rw [hf1 x hx]
      norm_num))
  have hσ : ContDiff ℝ ∞ (fun y => 2 * ∑ i ∈ t, f i y) :=
    contDiff_const.mul (ContDiff.sum fun i _ => hfd i)
  have hCc : IsCompact (⋃ i ∈ t, tsupport (f i)) := t.isCompact_biUnion fun i _ => hfc i
  have hCU : (⋃ i ∈ t, tsupport (f i)) ⊆ U := Set.iUnion₂_subset fun i _ => hfU i
  have hsuppC : Function.support (fun y => Real.smoothTransition (2 * ∑ i ∈ t, f i y)) ⊆
      ⋃ i ∈ t, tsupport (f i) := by
    intro y hy
    by_contra hyC
    apply hy
    have h0 : ∀ i ∈ t, f i y = 0 := fun i hi => by
      by_contra h
      exact hyC (Set.mem_biUnion hi (subset_tsupport _ h))
    show Real.smoothTransition (2 * ∑ i ∈ t, f i y) = 0
    rw [Finset.sum_eq_zero h0, mul_zero]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  have hts : tsupport (fun y => Real.smoothTransition (2 * ∑ i ∈ t, f i y)) ⊆ ⋃ i ∈ t, tsupport (f i) :=
    closure_minimal hsuppC hCc.isClosed
  refine ⟨fun y => Real.smoothTransition (2 * ∑ i ∈ t, f i y), Real.smoothTransition.contDiff.comp hσ,
    hCc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hCU, {y | 1 < 2 * ∑ i ∈ t, f i y},
    isOpen_lt continuous_const hσ.continuous, ?_, fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy)⟩
  intro x hx
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hcov hx)
  have : f i x ≤ ∑ j ∈ t, f j x := Finset.single_le_sum (fun j _ => hf0 j x) hi
  simp only [Set.mem_setOf_eq] at hix ⊢
  linarith

theorem contDiff_mul_of_tsupport {n : ℕ} {ρ f : (Fin n → ℂ) → ℝ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun y => ρ y * f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hρ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hy))
  · have hyρ : y ∉ tsupport ρ := fun h => hy (hρU h)
    have h0 : (fun z => ρ z * f z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyρ] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq h0

end Helpers

end

end ReciprocityTheory.AnForm.M.PLAux
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isClosed_of_isAnalyticSubset (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x (hx : x ∉ S)
  obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨j, hj⟩ := A.cover x
  have hxz : ¬ ∀ i, f i x = 0 := by
    intro hz
    have hmem : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hz⟩
    exact hx hmem.1
  push_neg at hxz
  obtain ⟨i, hi⟩ := hxz
  have hcont : ContinuousAt (f i) x := by
    have hxt : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]
      exact hxW
    have h1 : ContinuousAt (f i ∘ (A.chart j).symm) (A.chart j x) := (hf i j _ hxt).continuousAt
    have h3 := h1.comp ((A.chart j).continuousAt hj)
    refine h3.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hcont.eventually_ne hi, hWo.mem_nhds hxW] with y hy hyW
  intro hyS
  have hmem : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hmem
  exact hy (hmem.2 i)

theorem degree_det_restrictScalars (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    (L.restrictScalars ℝ).det =
      ‖LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h1 : (L.restrictScalars ℝ).det =
      LinearMap.det ((L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).restrictScalars ℝ) := rfl
  rw [h1, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem degree_sheet_chart_data {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V) :
    MeasurableSet ((B.chart j) '' W) ∧
    (A.chart k ∘ h ∘ (B.chart j).symm) '' ((B.chart j) '' W) = (A.chart k) '' V ∧
    Set.InjOn (A.chart k ∘ h ∘ (B.chart j).symm) ((B.chart j) '' W) ∧
    (∀ y ∈ (B.chart j) '' W, HasFDerivWithinAt (A.chart k ∘ h ∘ (B.chart j).symm)
      ((fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y).restrictScalars ℝ) ((B.chart j) '' W) y) ∧
    (∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source) := by
  have hWsrc : ∀ y ∈ (B.chart j) '' W, (B.chart j).symm y ∈ W ∧ y ∈ (B.chart j).target := by
    rintro y ⟨w, hw, rfl⟩
    refine ⟨?_, (B.chart j).map_source (hWj hw)⟩
    rw [(B.chart j).left_inv (hWj hw)]
    exact hw
  have hsrc : ∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source :=
    fun y hy => hVk (hbij.mapsTo (hWsrc y hy).1)
  refine ⟨?_, ?_, ?_, ?_, hsrc⟩
  · exact ((B.chart j).isOpen_image_of_subset_source hW hWj).measurableSet
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h ((B.chart j).symm y), hbij.mapsTo (hWsrc y hy).1, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hbij.surjOn hv
      refine ⟨B.chart j w, ⟨w, hw, rfl⟩, ?_⟩
      simp only [Function.comp_apply, (B.chart j).left_inv (hWj hw)]
  · rintro y₁ ⟨w₁, hw₁, rfl⟩ y₂ ⟨w₂, hw₂, rfl⟩ heq
    simp only [Function.comp_apply, (B.chart j).left_inv (hWj hw₁),
      (B.chart j).left_inv (hWj hw₂)] at heq
    have hww := hbij.injOn hw₁ hw₂
      ((A.chart k).injOn (hVk (hbij.mapsTo hw₁)) (hVk (hbij.mapsTo hw₂)) heq)
    rw [hww]
  · intro y hy
    have ha : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :=
      hh.2 j k y ⟨(hWsrc y hy).2, hsrc y hy⟩
    exact (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

theorem sheet_integral {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ℝ) :
    (IntegrableOn (fun y => f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y) ((B.chart j) '' W) ↔
      IntegrableOn (fun z => f ((A.chart k).symm z) * locDens A Φ k z) ((A.chart k) '' V)) ∧
    ∫ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y =
      ∫ z in (A.chart k) '' V, f ((A.chart k).symm z) * locDens A Φ k z := by
  obtain ⟨hU, himg, hinj, hder, hsrc⟩ := degree_sheet_chart_data hh j k hW hWj hVk hbij
  set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ
  set G : (Fin e → ℂ) → ℝ := fun z => f ((A.chart k).symm z) * locDens A Φ k z with hG
  have heq : Set.EqOn (fun y => f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y)
      (fun y => |((fderiv ℂ φ y).restrictScalars ℝ).det| • G (φ y)) ((B.chart j) '' W) := by
    intro y hy
    have hyT : y ∈ (B.chart j).target := by
      obtain ⟨w, hw, rfl⟩ := hy
      exact (B.chart j).map_source (hWj hw)
    simp only [hG, hφ, smul_eq_mul, degree_det_restrictScalars, Function.comp_apply,
      (A.chart k).left_inv (hsrc y hy)]
    rw [locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]
    simp only [abs_pow, abs_norm]
    ring
  refine ⟨?_, ?_⟩
  · rw [integrableOn_congr_fun heq hU, ← himg,
      integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU hder hinj G]
  · rw [setIntegral_congr_fun hU heq, ← himg,
      integral_image_eq_integral_abs_det_fderiv_smul volume hU hder hinj G]

theorem sheet_lintegral {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ENNReal) :
    ∫⁻ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j y| =
      ∫⁻ z in (A.chart k) '' V, f ((A.chart k).symm z) * ENNReal.ofReal |locDens A Φ k z| := by
  obtain ⟨hU, himg, hinj, hder, hsrc⟩ := degree_sheet_chart_data hh j k hW hWj hVk hbij
  set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU hder hinj]
  refine setLIntegral_congr_fun hU fun y hy => ?_
  have hyT : y ∈ (B.chart j).target := by
    obtain ⟨w, hw, rfl⟩ := hy
    exact (B.chart j).map_source (hWj hw)
  simp only [hφ, degree_det_restrictScalars, Function.comp_apply,
    (A.chart k).left_inv (hsrc y hy)]
  rw [locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]
  simp only [abs_mul, abs_pow, abs_norm]
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  ring

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem maMeasure_thm : MaMeasureStatement := by
  intro e X _ _ _ _ _ A Φ hΦ hPsh
  have hne : Nonempty (ChartPartition A) := existsPartition A
  refine ⟨?_, fun g hg => ⟨⟨fun hgi => (maMeasure_forward A Φ hΦ hPsh hg hgi).1,
    fun hgi => maMeasure_converse A Φ hΦ hPsh hg hgi⟩,
    fun hgi => (maMeasure_forward A Φ hΦ hPsh hg hgi).2⟩⟩

  rw [maMeasure_eq_sum A Φ hne]
  haveI : ∀ j, IsFiniteMeasure (chartMeasure A hne.some Φ j) := fun j =>
    chartMeasure_finite A hne.some Φ hΦ hPsh j
  infer_instance
theorem maMeasureMono : MaMeasureMonoStatement := by
  intro e X _ _ _ A Φ Θ hΦ hΦp hΘ hΘp
  exact maMeasure_mono_of_psh A Φ Θ hΦ hΦp hΘ hΘp

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem st_smooth_continuous (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j).continuousOn.continuousAt (by
      rw [Set.preimage_univ, Set.inter_univ]
      exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem st_smooth_mul (A : FinHolAtlas e X) {f g : X → ℝ} (hf : A.Smooth f) (hg : A.Smooth g) :
    A.Smooth (fun x => f x * g x) := fun j => (hf j).mul (hg j)

theorem st_smooth_const (A : FinHolAtlas e X) (c : ℝ) : A.Smooth (fun _ => c) := fun j => contDiffOn_const

theorem st_smooth_sum (A : FinHolAtlas e X) {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ m, A.Smooth (f m)) : A.Smooth (fun x => ∑ m ∈ s, f m x) := fun j => ContDiffOn.sum fun m _ => hf m j

theorem st_mInt_congr_phi (A : FinHolAtlas e X) {Φ Ψ : Fin e → LocPot X}
    (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  have h1 : ∀ j y, locDens A Φ j y = locDens A Ψ j y := fun j y => by
    unfold locDens; simp only [h]
  unfold mInt integralWith
  simp only [h1]

theorem st_mInt_zero (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) :
    mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt integralWith
  split_ifs <;> simp

theorem st_hessC_eq_zero {D : ℕ} {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (c : ℝ)
    (h : f =ᶠ[𝓝 y] fun _ => c) : hessC f y = 0 := by
  have h1 : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun _ : Fin D → ℂ => c) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => c)) y :=
    h1.fderiv_eq
  have h3 : fderiv ℝ (fun _ : Fin D → ℂ => c) = fun _ => 0 := by
    funext z; simp
  ext i k
  simp only [hessC, h2, h3]
  simp

theorem st_maDens_cons_eq_zero {n : ℕ} (φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (h : hessC (φ 0) y = 0) : maDens φ y = 0 := by
  have hm : (fun k => hessC (φ k) y) =
      (Fin.cons (hessC (φ 0) y) (fun i : Fin n => hessC (φ i.succ) y) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    funext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDens, hm, h, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum]
  simp

theorem st_locDens_cons_eq_zero (A : FinHolAtlas (e + 1) X) (k : Fin A.n) (ψ : X → ℝ)
    (Φ : Fin e → LocPot X) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart k).target)
    (hψ : (A.chart k).symm y ∉ tsupport ψ) :
    locDens A (Fin.cons (LocPot.ofFun ψ) Φ) k y = 0 := by
  unfold locDens
  apply st_maDens_cons_eq_zero
  apply st_hessC_eq_zero 0
  have h1 : (tsupport ψ)ᶜ ∈ 𝓝 ((A.chart k).symm y) := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hψ
  have h2 := ((A.chart k).continuousAt_symm hy).preimage_mem_nhds h1
  filter_upwards [h2] with y' hy'
  first
  | exact image_eq_zero_of_notMem_tsupport hy'
  | exact image_eq_zero_of_nmem_tsupport hy'

theorem st_mIntConstPot (A : FinHolAtlas (e + 1) X) (c : ℝ) (Φ : Fin e → LocPot X)
    (g : X → ℝ) : mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0 := by
  unfold mInt integralWith
  split_ifs
  · refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : ∀ y, locDens A (Fin.cons (LocPot.ofFun fun _ => c) Φ) j y = 0 := by
      intro y
      unfold locDens
      apply st_maDens_cons_eq_zero
      exact st_hessC_eq_zero c (Filter.Eventually.of_forall fun _ => rfl)
    simp [h0]
  · rfl

theorem st_isPotential_cons (A : FinHolAtlas (e + 1) X) {u : X → ℝ} (hu : A.Smooth u)
    {Φ : Fin e → LocPot X} (hΦ : ∀ i, IsPotential A (Φ i)) :
    ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun u) Φ : Fin (e + 1) → LocPot X) i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · show IsPotential A (LocPot.ofFun u)
    exact ⟨fun x => hu, fun x x' y _ => ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
      fun j => analyticOnNhd_const, fun z _ => by simp [LocPot.ofFun]⟩⟩
  · show IsPotential A (Φ i)
    exact hΦ i

theorem st_mInt_finset_sum [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, Continuous (f m)) :
    mInt A Φ (fun x => ∑ m ∈ s, f m x) = ∑ m ∈ s, mInt A Φ (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_mInt_zero A Φ
  | insert a s ha ih =>
    have hc : Continuous (fun x => ∑ m ∈ s, f m x) := continuous_finsetSum _ fun m _ => hf m
    have := mIntLinear A Φ hΦ 1 (f a) (fun x => ∑ m ∈ s, f m x)
      (mIntegrableCont A Φ hΦ _ (hf a)) (mIntegrableCont A Φ hΦ _ hc)
    simp only [one_mul] at this
    simp only [Finset.sum_insert ha, this, ih]

theorem st_mInt_cons_finset_sum [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, A.Smooth (f m)) (g : X → ℝ) (hg : Continuous g) :
    mInt A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) g =
      ∑ m ∈ s, mInt A (Fin.cons (LocPot.ofFun (f m)) Φ) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_mIntConstPot A 0 Φ g
  | insert a s ha ih =>
    have hS : A.Smooth (fun x => ∑ m ∈ s, f m x) := st_smooth_sum A s hf
    have hcongr : mInt A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ insert a s, f m x) Φ) g =
        mInt A (Fin.cons (LocPot.ofFun (f a) + LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) g := by
      apply st_mInt_congr_phi
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · funext x y
        simp [Finset.sum_insert ha, LocPot.ofFun]
        rfl
      · rfl
    rw [hcongr, mIntAdd A _ _ Φ (isPotential_ofFun A _ (hf a)) (isPotential_ofFun A _ hS) hΦ g
      (mIntegrableCont A _ (st_isPotential_cons A (hf a) hΦ) g hg)
      (mIntegrableCont A _ (st_isPotential_cons A hS hΦ) g hg), ih, Finset.sum_insert ha]

end

end ReciprocityTheory.AnForm.M
end

