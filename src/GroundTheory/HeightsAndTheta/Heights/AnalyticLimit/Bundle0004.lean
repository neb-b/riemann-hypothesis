module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLocDensContOnOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens potSmoothOn hessCGerm maDens_congr_hessC
  maDens_continuousOn)

theorem LocDensContOnOpen.proof : LocDensContOnOpen.Statement := by
  intro D X _ A Yo th u hYo hth hu j y0 hy0
  apply ContinuousAt.continuousWithinAt
  have hu2 : ∀ i, ContDiffOn ℝ 2 (u i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    fun i => (hu i j).of_le (WithTop.coe_le_coe.2 le_top)
  have hNo : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) :=
    (A.chart j).isOpen_inter_preimage_symm
      (hYo.inter (isOpen_iInter_of_finite fun i => (th i).isOpen_U _))
  have hy0N : y0 ∈ (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)) :=
    ⟨hy0.1, hy0.2, Set.mem_iInter.2 fun i => (th i).mem_U _⟩
  have hsm : ∀ i, ContDiffOn ℝ 2 (fun y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) ((A.chart j).target ∩
        (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) := fun i =>
    ((potSmoothOn A (th i) (hth i) _ j).mono (t := (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)))
      fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i⟩).add
      ((hu2 i).mono (t := (A.chart j).target ∩
        (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)))
        fun y hy => ⟨hy.1, hy.2.1⟩)
  have heq : ReciprocityTheory.AnForm.maDens (fun i y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) =ᶠ[nhds y0] locDens A (fun i => potForm (th i) (u i)) j := by
    filter_upwards [hNo.mem_nhds hy0N] with y hy
    unfold locDens
    apply maDens_congr_hessC
    intro i
    have hp0 : (A.chart j).symm y ∈ (th i).U ((A.chart j).symm y0) := Set.mem_iInter.1 hy.2.2 i
    obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ :=
      (hth i).2 ((A.chart j).symm y) ((A.chart j).symm y0) ((A.chart j).symm y) ⟨(th i).mem_U _, hp0⟩
    have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0))) :=
      (A.chart j).isOpen_inter_preimage_symm
        ((hWo.inter ((th i).isOpen_U _)).inter ((th i).isOpen_U _))
    have hyV : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0)) :=
      ⟨hy.1, ⟨hyW, (th i).mem_U _⟩, hp0⟩
    have h1 : (fun y' => (potForm (th i) (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
        (fun w => ((th i).φ ((A.chart j).symm y0) ((A.chart j).symm w) + u i ((A.chart j).symm w)) +
          ((G ∘ (A.chart j).symm) w).re) := by
      filter_upwards [hVo.mem_nhds hyV] with w hw
      have := hGeq ((A.chart j).symm w) hw.2
      show (th i).φ _ _ + u i _ = _
      simp only [Function.comp_apply]
      linarith
    exact ((hessCGerm _ _ _ h1).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
      ((hsm i).contDiffAt (hNo.mem_nhds hy)) (hG j y ⟨hy.1, hyW⟩))).symm
  refine ContinuousAt.congr ?_ heq
  exact (maDens_continuousOn _ _ hNo hsm).continuousAt (hNo.mem_nhds hy0N)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntegrableOfDensLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens MIntegrable)

theorem MIntegrableOfDensLe.proof : MIntegrableOfDensLe.Statement := by
  intro D X _ A V Φ Ψ hV hΦc hΨc hle g hg hΨ j K hK hKc
  set e := A.chart j
  set dΦ := locDens A Φ j
  set dΨ := locDens A Ψ j
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  set W := (e.target ∩ e.symm ⁻¹' V) ∩ dΨ ⁻¹' Set.Ioi 0 with hWdef
  have hW : IsOpen W := (hΨc j).isOpen_inter_preimage hO isOpen_Ioi
  set q : (Fin D → ℂ) → ℝ := W.indicator (fun y => dΦ y / dΨ y) with hqdef
  have hqc : ContinuousOn (fun y => dΦ y / dΨ y) W :=
    ((hΦc j).mono Set.inter_subset_left).div ((hΨc j).mono Set.inter_subset_left)
      (fun y hy => (ne_of_gt hy.2))
  have hqm : AEStronglyMeasurable q (volume.restrict K) :=
    ((aestronglyMeasurable_indicator_iff hW.measurableSet).2
      (hqc.aestronglyMeasurable hW.measurableSet)).restrict
  have hqb : ∀ y, ‖q y‖ ≤ 1 := by
    intro y
    by_cases hy : y ∈ W
    · have hpos : 0 < dΨ y := hy.2
      obtain ⟨h0, h1⟩ := hle j y hy.1.1 hy.1.2
      rw [hqdef, Set.indicator_of_mem hy, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg h0 hpos.le)]
      exact (div_le_one hpos).2 h1
    · rw [hqdef, Set.indicator_of_notMem hy, norm_zero]
      exact zero_le_one
  have hint : IntegrableOn (fun y => (g (e.symm y) * dΨ y) * q y) K :=
    Integrable.mul_bdd (hΨ j K hK hKc) hqm (Filter.Eventually.of_forall hqb)
  refine hint.congr_fun ?_ hKc.measurableSet
  intro y hy
  have hyt : y ∈ e.target := hK hy
  simp only
  by_cases hyV : e.symm y ∈ V
  · obtain ⟨h0, h1⟩ := hle j y hyt hyV
    by_cases hpos : 0 < dΨ y
    · have hyW : y ∈ W := ⟨⟨hyt, hyV⟩, hpos⟩
      rw [hqdef, Set.indicator_of_mem hyW]
      field_simp
    · have hyW : y ∉ W := fun h => hpos h.2
      have hz : dΦ y = 0 := le_antisymm (h1.trans (not_lt.1 hpos)) h0
      rw [hqdef, Set.indicator_of_notMem hyW, hz]
      ring
  · rw [hg _ hyV]
    ring

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPropertyF
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax Mollifier)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errE errorWithLinear ell)

noncomputable section

section C2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendstoUniformlyOn_finset_biUnion {α β ι κ : Type*} [UniformSpace β] {F : κ → α → β}
    {f : α → β} {p : Filter κ} (T : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ T, TendstoUniformlyOn F f p (S i)) : TendstoUniformlyOn F f p (⋃ i ∈ T, S i) := by
  intro u hu
  filter_upwards [(eventually_all_finset T).2 fun i hi => h i hi u hu] with n hn x hx
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 hx
  exact hn i hi x hx

theorem TendstoC2On.congr_open {F G : ℝ → E → ℝ} {f : E → ℝ} {L U : Set E} (hU : IsOpen U)
    (hLU : L ⊆ U) (hFG : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ U, F t y = G t y) (h : TendstoC2On G f L) :
    TendstoC2On F f L := by
  have e0 : ∀ t, (∀ y ∈ U, F t y = G t y) → ∀ y ∈ U, F t =ᶠ[𝓝 y] G t :=
    fun t ht y hy => Filter.eventually_of_mem (hU.mem_nhds hy) ht
  refine ⟨h.1.congr ?_, h.2.1.congr ?_, h.2.2.congr ?_⟩
  · filter_upwards [hFG] with t ht y hy
    exact (ht y (hLU hy)).symm
  · filter_upwards [hFG] with t ht y hy
    exact (e0 t ht y (hLU hy)).fderiv_eq.symm
  · filter_upwards [hFG] with t ht y hy
    have h' : fderiv ℝ (F t) =ᶠ[𝓝 y] fderiv ℝ (G t) :=
      Filter.eventually_of_mem (hU.mem_nhds (hLU hy)) fun z hz => (e0 t ht z hz).fderiv_eq
    exact h'.fderiv_eq.symm

end C2

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

def LemmaETailMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailMassBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def RegSection.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ (L : LocPot X) (s : X → X → ℂ), IsPotential A L ∧ IsSection A L s ∧
      (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) ∧ secOpen s = R.Yo ∧ Dense R.Yo ∧
      ContinuousOn R.r R.Yo ∧ ContinuousOn (rSec L s) R.Yo ∧
      ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec L s y| ≤ B

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def TailShift.Statement : Prop :=
  ∀ (D : ℕ) (B CE : ℝ), ∃ CE' : ℝ, ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas D X) (Yo : Set X) (r r' : X → ℝ) (T : Fin D → LocPot X),
    IsOpen Yo → ContinuousOn r Yo → ContinuousOn r' Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → (∀ x ∈ Yo, Real.exp 1 ≤ r' x) →
    (∀ x ∈ Yo, |r x - r' x| ≤ B) →
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A T j y) →
    TailLogBound A Yo r' T CE → TailLogBound A Yo r T CE'

section Inhabitants

open ReciprocityTheory.AnForm (fsDens fsDens_pos)
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLine_locDens_first_chart projectiveLine_locDens_second_chart projectiveLine_fubiniStudy_mass_one)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

