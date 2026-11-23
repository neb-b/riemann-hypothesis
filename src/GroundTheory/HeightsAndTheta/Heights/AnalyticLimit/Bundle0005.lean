module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)

theorem log_le_one_add_mul_log {a b B : ℝ} (ha : Real.exp 1 ≤ a) (hb : 0 < b) (hB : 0 ≤ B)
    (hab : b ≤ a + B) : Real.log b ≤ (1 + B) * Real.log a := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < a := by linarith
  have hla : 1 ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  have h1 : b ≤ a * (1 + B) := by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ a by linarith) hB]
  have h2 : Real.log b ≤ Real.log a + Real.log (1 + B) := by
    rw [← Real.log_mul ha0.ne' (by linarith)]
    exact Real.log_le_log hb h1
  have h3 : Real.log (1 + B) ≤ B := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + B by linarith)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hla hB]

theorem ListTailLog.proof (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement := by
  intro X _ _ _ D A R hr Om C₁
  obtain ⟨L, s, hL, hs, hs1, hYo, hden, hrc, hrEc, B, hB⟩ := hC D A R
  have hrE : ∀ x ∈ R.Yo, Real.exp 1 ≤ rSec L s x := fun x hx => by
    rw [← hYo] at hx
    have hpos : 0 < ‖s x x‖ * Real.exp (-L.φ x x) :=
      mul_pos (norm_pos_iff.2 hx) (Real.exp_pos _)
    have : logNormSec L s x ≤ 0 := Real.log_nonpos hpos.le (hs1 x)
    simp only [rSec]
    linarith
  have hC₁ : 0 ≤ max C₁ 0 * (1 + max B 0) :=
    mul_nonneg (le_max_right _ _) (by linarith [le_max_right B 0])
  obtain ⟨CE, hCE⟩ := hE D A Om L s hL hs (hYo ▸ hden) hs1 _ hC₁
  obtain ⟨CE', hCE'⟩ := hS D (max B 0) CE
  refine ⟨CE', fun th u hT => ?_⟩
  obtain ⟨hA, hpos, hmono⟩ := hM D A R.Yo R.r Om C₁ th u R.isOpen_Yo hT
  have hu : ∀ i, IsLemmaEPot A Om L s (max C₁ 0 * (1 + max B 0)) (u i) := fun i => by
    have hTi := hT i
    refine ⟨by rw [hYo]; exact hTi.u_smooth, by rw [hYo]; exact hA i,
      by rw [hYo]; exact hTi.u_nonpos, fun x hx => ?_, ?_⟩
    · rw [hYo] at hx
      have hl := log_le_one_add_mul_log (b := R.r x) (hrE x hx) (by linarith [hr x hx, Real.exp_pos 1])
        (le_max_right B 0) (by linarith [(abs_le.1 (hB x hx)).2, le_max_left B 0])
      have h0 : 0 ≤ Real.log (R.r x) :=
        Real.log_nonneg (by linarith [hr x hx, Real.add_one_le_exp (1 : ℝ)])
      have := mul_le_mul_of_nonneg_left hl (le_max_right C₁ 0)
      have := mul_le_mul_of_nonneg_right (le_max_left C₁ 0) h0
      have := hTi.le_u x hx
      nlinarith
    · rcases hTi.smooth_or_pole with h | h
      · exact Or.inl h
      · right
        rw [hYo]
        exact h
  have h2 : TailLogBound A R.Yo (rSec L s) (fun j => potForm (th j) (u j)) CE := by
    have h1 := hCE u hu
    rw [hYo] at h1
    intro R₀ hR₀
    obtain ⟨hi, hle⟩ := h1 R₀ hR₀
    obtain ⟨hi', hle'⟩ := hmono _
      (fun x => Set.indicator_nonneg (fun y hy => Real.log_nonneg
        (by linarith [hrE y hy.1, Real.add_one_le_exp (1 : ℝ)])) x)
      (fun x hx => Set.indicator_of_notMem (by exact fun h => hx h.1) _) hi
    exact ⟨hi', hle'.trans hle⟩
  exact hCE' A R.Yo R.r (rSec L s) _ R.isOpen_Yo hrc hrEc hr hrE
    (fun x hx => (hB x hx).trans (le_max_left B 0)) hpos h2

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

theorem log_le_of_abs_sub_le {B a b : ℝ} (hb : Real.exp 1 ≤ b) (ha : 0 < a) (hab : |a - b| ≤ B) :
    Real.log a ≤ (1 + max B 0) * Real.log b := by
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) hb
  have hlb : 1 ≤ Real.log b := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hb
  have hB : 0 ≤ max B 0 := le_max_right _ _
  have hb1 : 1 ≤ b := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hb
  have h1 : a ≤ b * (1 + max B 0) := by
    have := (abs_le.1 hab).2
    have := le_max_left B 0
    nlinarith [mul_nonneg (sub_nonneg.2 hb1) hB]
  calc Real.log a ≤ Real.log (b * (1 + max B 0)) := Real.log_le_log ha h1
    _ = Real.log b + Real.log (1 + max B 0) := Real.log_mul hb0.ne' (by positivity)
    _ ≤ Real.log b + max B 0 := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + max B 0 by positivity)]
    _ ≤ (1 + max B 0) * Real.log b := by nlinarith [mul_nonneg hB (sub_nonneg.2 hlb)]

theorem TailShift.proof : TailShift.Statement := by
  intro D B CE
  set Bp := max B 0 with hBpdef
  set R1 := max (Real.exp 1 + Bp) (2 * Bp)
  refine ⟨2 * (1 + Bp) * max CE 0 * R1, ?_⟩
  intro X _ _ _ A Yo r r' T hYo hr hr' hre hr'e hB hdens hT
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have he := Real.exp_pos 1
  have hBp : 0 ≤ Bp := le_max_right _ _
  have hlog : ∀ x ∈ Yo, Real.log (r x) ≤ (1 + Bp) * Real.log (r' x) := fun x hx =>
    log_le_of_abs_sub_le (hr'e x hx) (lt_of_lt_of_le he (hre x hx)) (hB x hx)
  have hl' : ∀ x ∈ Yo, 1 ≤ Real.log (r' x) := fun x hx => by
    rw [← Real.log_exp 1]; exact Real.log_le_log he (hr'e x hx)
  have hl : ∀ x ∈ Yo, 1 ≤ Real.log (r x) := fun x hx => by
    rw [← Real.log_exp 1]; exact Real.log_le_log he (hre x hx)

  have key : ∀ R₀ R', Real.exp 1 ≤ R' → (∀ x ∈ Yo, R₀ ≤ r x → R' ≤ r' x) →
      mInt A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) ≤
        (1 + Bp) * mInt A T ((tail Yo r' R').indicator fun x => Real.log (r' x)) := by
    intro R₀ R' hR' hsub
    refine mInt_le_mul_of_le A T Yo (hT R' hR').1 hdens (fun x => ?_)
      (fun x hx => Set.indicator_of_notMem (by exact fun h => hx h.1) _)
      (fun x hx => Set.indicator_of_notMem (by exact fun h => hx h.1) _) (fun x hx => ?_)
    · by_cases h : x ∈ tail Yo r R₀
      · rw [Set.indicator_of_mem h]; linarith [hl x h.1]
      · rw [Set.indicator_of_notMem h]
    · by_cases h : R₀ ≤ r x
      · rw [Set.indicator_of_mem (show x ∈ tail Yo r R₀ from ⟨hx, h⟩),
          Set.indicator_of_mem (show x ∈ tail Yo r' R' from ⟨hx, hsub x hx h⟩)]
        exact hlog x hx
      · rw [Set.indicator_of_notMem (show x ∉ tail Yo r R₀ from fun h' => h h'.2)]
        by_cases h' : R' ≤ r' x
        · rw [Set.indicator_of_mem (show x ∈ tail Yo r' R' from ⟨hx, h'⟩)]
          nlinarith [hl' x hx]
        · rw [Set.indicator_of_notMem (show x ∉ tail Yo r' R' from fun h'' => h' h''.2)]; simp

  have hint : ∀ R₀, MIntegrable A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) := by
    intro R₀ j K hK hKc
    have htm : MeasurableSet (tail Yo r R₀) := by
      have : tail Yo r R₀ = Yo \ (Yo ∩ r ⁻¹' Set.Iio R₀) := by
        ext x
        simp only [tail, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_Iio, not_and, not_lt]
        exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
      rw [this]
      exact hYo.measurableSet.diff (hr.isOpen_inter_preimage hYo isOpen_Iio).measurableSet
    have hGc : ContinuousOn (fun x => Real.log (r x) / Real.log (r' x)) (tail Yo r R₀) :=
      ((hr.log fun x hx => (lt_of_lt_of_le he (hre x hx)).ne').div
        (hr'.log fun x hx => (lt_of_lt_of_le he (hr'e x hx)).ne')
        fun x hx => (lt_of_lt_of_le one_pos (hl' x hx)).ne').mono fun x hx => hx.1
    classical
    have hGm : Measurable ((tail Yo r R₀).indicator fun x => Real.log (r x) / Real.log (r' x)) := by
      have := hGc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) htm
      convert this using 1
      funext x
      simp [Set.indicator, Set.piecewise]
    have hT' : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    have hsm : AEMeasurable (fun y => (tail Yo r R₀).indicator
        (fun x => Real.log (r x) / Real.log (r' x)) ((A.chart j).symm y)) (volume.restrict K) :=
      (hGm.comp_aemeasurable ((A.chart j).continuousOn_symm.aemeasurable hT')).mono_measure
        (Measure.restrict_mono hK le_rfl)
    have hid : ∀ x, (tail Yo r R₀).indicator (fun x => Real.log (r x)) x =
        (tail Yo r R₀).indicator (fun x => Real.log (r x) / Real.log (r' x)) x *
          (tail Yo r' (Real.exp 1)).indicator (fun x => Real.log (r' x)) x := by
      intro x
      by_cases h : x ∈ tail Yo r R₀
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h,
          Set.indicator_of_mem (show x ∈ tail Yo r' (Real.exp 1) from ⟨h.1, hr'e x h.1⟩),
          div_mul_cancel₀ _ (lt_of_lt_of_le one_pos (hl' x h.1)).ne']
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    have e1 : (fun y => (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) *
        locDens A T j y) = fun y => (tail Yo r R₀).indicator
          (fun x => Real.log (r x) / Real.log (r' x)) ((A.chart j).symm y) *
          ((tail Yo r' (Real.exp 1)).indicator (fun x => Real.log (r' x)) ((A.chart j).symm y) *
            locDens A T j y) := by
      funext y
      rw [hid, mul_assoc]
    rw [e1]
    refine Integrable.bdd_mul (c := 1 + Bp) ((hT (Real.exp 1) le_rfl).1 j K hK hKc)
      hsm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : (A.chart j).symm y ∈ tail Yo r R₀
    · rw [Set.indicator_of_mem h]
      have h1 := hl' _ h.1
      have h3 := hl _ h.1
      rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith)), div_le_iff₀ (by linarith)]
      exact hlog _ h.1
    · rw [Set.indicator_of_notMem h, abs_zero]
      linarith

  intro R₀ hR₀
  refine ⟨hint R₀, ?_⟩
  have hlR : 1 ≤ Real.log R₀ := by rw [← Real.log_exp 1]; exact Real.log_le_log he hR₀
  have hR0 : 0 < R₀ := lt_of_lt_of_le he hR₀
  have hR1a : Real.exp 1 + Bp ≤ R1 := le_max_left _ _
  have hR1b : 2 * Bp ≤ R1 := le_max_right _ _
  have hCE : CE ≤ max CE 0 := le_max_left _ _
  have hCE0 : 0 ≤ max CE 0 := le_max_right _ _
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL0 : 0 ≤ Real.log R₀ ^ (D + 1) := pow_nonneg (by linarith) _
  have hL1 : 1 ≤ Real.log R₀ ^ (D + 1) := one_le_pow₀ hlR
  have hBp1 : 0 ≤ 1 + Bp := by linarith
  by_cases hbig : R1 ≤ R₀
  · have hR' : Real.exp 1 ≤ R₀ - Bp := by linarith
    have hpos : 0 < R₀ - Bp := by linarith
    refine (key R₀ (R₀ - Bp) hR' fun x hx h => ?_).trans ?_
    · have := (abs_le.1 (hB x hx)).2
      linarith [le_max_left B 0]
    have hb := (hT (R₀ - Bp) hR').2
    have hlog1 : 0 ≤ Real.log (R₀ - Bp) := Real.log_nonneg (by linarith)
    have hpow : Real.log (R₀ - Bp) ^ (D + 1) ≤ Real.log R₀ ^ (D + 1) :=
      pow_le_pow_left₀ hlog1 (Real.log_le_log hpos (by linarith)) _
    have s1 : CE * Real.log (R₀ - Bp) ^ (D + 1) / (R₀ - Bp) ≤
        max CE 0 * Real.log R₀ ^ (D + 1) / (R₀ - Bp) :=
      div_le_div_of_nonneg_right (mul_le_mul hCE hpow (pow_nonneg hlog1 _) hCE0) hpos.le
    have s2 : max CE 0 * Real.log R₀ ^ (D + 1) / (R₀ - Bp) ≤
        max CE 0 * Real.log R₀ ^ (D + 1) * 2 / R₀ := by
      rw [div_le_div_iff₀ hpos hR0]
      nlinarith [mul_nonneg (mul_nonneg hCE0 hL0) (show 0 ≤ 2 * (R₀ - Bp) - R₀ by linarith)]
    have s3 : 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) ≤
        2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) := by
      have h0 : 0 ≤ 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) := by positivity
      nlinarith [mul_nonneg h0 (show 0 ≤ R1 - 1 by linarith)]
    calc (1 + Bp) * mInt A T ((tail Yo r' (R₀ - Bp)).indicator fun x => Real.log (r' x))
        ≤ (1 + Bp) * (max CE 0 * Real.log R₀ ^ (D + 1) * 2 / R₀) :=
          mul_le_mul_of_nonneg_left (hb.trans (s1.trans s2)) hBp1
      _ = 2 * (1 + Bp) * max CE 0 * Real.log R₀ ^ (D + 1) / R₀ := by ring
      _ ≤ 2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) / R₀ :=
          div_le_div_of_nonneg_right s3 hR0.le
  · replace hbig := not_le.1 hbig
    refine (key R₀ (Real.exp 1) le_rfl fun x hx _ => hr'e x hx).trans ?_
    have hb := (hT (Real.exp 1) le_rfl).2
    rw [Real.log_exp, one_pow, mul_one] at hb
    have s1 : CE / Real.exp 1 ≤ max CE 0 := by
      rw [div_le_iff₀ he]; nlinarith [mul_nonneg hCE0 (show 0 ≤ Real.exp 1 - 1 by linarith)]
    have hZ : 0 ≤ (1 + Bp) * max CE 0 := mul_nonneg hBp1 hCE0
    have s2 : R₀ ≤ 2 * R1 * Real.log R₀ ^ (D + 1) := by nlinarith
    calc (1 + Bp) * mInt A T ((tail Yo r' (Real.exp 1)).indicator fun x => Real.log (r' x))
        ≤ (1 + Bp) * max CE 0 := mul_le_mul_of_nonneg_left (hb.trans s1) hBp1
      _ ≤ 2 * (1 + Bp) * max CE 0 * R1 * Real.log R₀ ^ (D + 1) / R₀ := by
          rw [le_div_iff₀ hR0]
          nlinarith [mul_le_mul_of_nonneg_left s2 hZ]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

noncomputable section

section Objects

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def bdDom (R : RegChartData A) (j : Fin R.n) : Set X := (R.ψ j).source ∩ R.ψ j ⁻¹' R.W j

theorem isOpen_bdDom (R : RegChartData A) (j : Fin R.n) : IsOpen (bdDom R j) :=
  (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j)

def bdEq (R : RegChartData A) (j : Fin R.n) (y : X) : ℂ := ∏ i ∈ R.S j, R.ψ j y i

def bdIdx (R : RegChartData A) (x : X) : Fin R.n := (R.cover x).choose

theorem mem_V''_bdIdx (R : RegChartData A) (x : X) : x ∈ R.V'' (bdIdx R x) :=
  (R.cover x).choose_spec

theorem V''_subset_bdDom (R : RegChartData A) (j : Fin R.n) : R.V'' j ⊆ bdDom R j :=
  fun _ hx => ⟨hx.1, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hx.2)))⟩

theorem mem_bdDom_bdIdx (R : RegChartData A) (x : X) : x ∈ bdDom R (bdIdx R x) :=
  V''_subset_bdDom R _ (mem_V''_bdIdx R x)

def bdPot (R : RegChartData A) (φ : Fin R.n → X → ℝ) (c : ℝ) : LocPot X where
  U x := bdDom R (bdIdx R x)
  isOpen_U _ := isOpen_bdDom R _
  mem_U x := mem_bdDom_bdIdx R x
  φ x y := φ (bdIdx R x) y + c

def bdSec (R : RegChartData A) (x : X) : X → ℂ := bdEq R (bdIdx R x)

def IsBdMetric (R : RegChartData A) (φ : Fin R.n → X → ℝ) : Prop :=
  (∀ j, A.SmoothOn (bdDom R j) (φ j)) ∧
  (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
      A.HoloOn W G ∧ ∀ z ∈ W ∩ (bdDom R j ∩ bdDom R k), φ j z - φ k z = (G z).re) ∧
  ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
    ‖bdEq R j y‖ * Real.exp (-φ j y) = ‖bdEq R k y‖ * Real.exp (-φ k y)

def bdWeight (R : RegChartData A) (χ : Fin R.n → X → ℝ) (g : Fin R.n → Fin R.n → X → ℂ)
    (j : Fin R.n) (y : X) : ℝ :=
  ∑ l, (bdDom R l).indicator (fun z => χ l z * ‖g j l z‖ ^ 2) y

end Objects

def RegYoDense.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A), Dense R.Yo

def RegRCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A),
    ContinuousOn R.r R.Yo

def ChartCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X), IsOpen U →
    (∀ f : X → ℝ, A.SmoothOn U f → ContinuousOn f U) ∧
    ∀ g : X → ℂ, A.HoloOn U g → ContinuousOn g U

def BdEqHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n),
    A.HoloOn (bdDom R j) (bdEq R j) ∧ ∀ y ∈ bdDom R j, (bdEq R j y = 0 ↔ y ∉ R.Yo)

def HyperplaneDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (i : Fin D), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z i = 0 → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = z i * G z

def CoordDivDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (S : Finset (Fin D)), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z ∈ coordDiv S → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = (∏ i ∈ S, z i) * G z

def BdDivides.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ u : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) u ∧ ContinuousOn u (bdDom R j ∩ bdDom R k) ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R k y = u y * bdEq R j y

def BdTransition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ g : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) g ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, g y ≠ 0 ∧ bdEq R j y = g y * bdEq R k y

def BdCocycle.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (g : Fin R.n → Fin R.n → X → ℂ), (∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R j y = g j k y * bdEq R k y) →
    ∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y

def BdPartition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ χ : Fin R.n → X → ℝ, (∀ j, A.Smooth (χ j)) ∧ (∀ j y, 0 ≤ χ j y) ∧
      (∀ y, ∑ j, χ j y = 1) ∧ ∀ j, tsupport (χ j) ⊆ bdDom R j

def LogNormHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (W : Set X) (g : X → ℂ),
    IsOpen W → A.HoloOn W g → (∀ y ∈ W, g y ≠ 0) → ∀ y ∈ W, ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re

def IndicatorSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U O : Set X) (χ h : X → ℝ),
    IsOpen U → IsOpen O → A.Smooth χ → tsupport χ ⊆ O → A.SmoothOn (U ∩ O) h →
    A.SmoothOn U (O.indicator fun y => χ y * h y)

def NormSqSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X) (g : X → ℂ),
    A.HoloOn U g → A.SmoothOn U (fun y => ‖g y‖ ^ 2)

def BdWeight.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (g : Fin R.n → Fin R.n → X → ℂ),
    (∀ j k, A.HoloOn (bdDom R j ∩ bdDom R k) (g j k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, g j k y ≠ 0) →
    (∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y) →
    ∃ w : Fin R.n → X → ℝ, (∀ j, A.SmoothOn (bdDom R j) (w j)) ∧
      (∀ j, ∀ y ∈ bdDom R j, 0 < w j y) ∧
      ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, w j y = ‖g j k y‖ ^ 2 * w k y

def BdMetric.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ φ : Fin R.n → X → ℝ, IsBdMetric R φ

def BddOnInner.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n)
    (u : X → ℝ), ContinuousOn u (bdDom R j) → ∃ B : ℝ, ∀ y ∈ R.V'' j, |u y| ≤ B

def BdSectionProps.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    IsPotential A (bdPot R φ c) ∧ IsSection A (bdPot R φ c) (bdSec R) ∧ secOpen (bdSec R) = R.Yo

def BdNormCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    Continuous fun y => ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)

def BdComparison.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec (bdPot R φ c) (bdSec R) y| ≤ B

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 holoOn_const)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StatementsPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart levi_base_indep)

noncomputable section

def C2ConvOn {E : ℕ} {Z : Type} [TopologicalSpace Z] (A : FinHolAtlas E Z) (V : Set Z)
    (g : ℝ → Z → ℝ) (φ : Z → ℝ) : Prop :=
  ∀ (k : Fin A.n) (K : Set (Fin E → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V →
    TendstoUniformlyOn (fun t y => g t ((A.chart k).symm y)) (fun y => φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K

def C2ConvergencePullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (B : FinHolAtlas D Y)
    (A : FinHolAtlas E Z) (f : Y → Z), HoloMap B A f →
    ∀ (V : Set Z), IsOpen V → ∀ (g : ℝ → Z → ℝ) (φ : Z → ℝ) (φ' : Y → ℝ),
      A.SmoothOn V φ → (∀ y ∈ f ⁻¹' V, φ' y = φ (f y)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (g t)) →
      C2ConvOn A V g φ → C2ConvOn B (f ⁻¹' V) (fun t => g t ∘ f) φ'

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

