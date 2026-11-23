module

public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0616

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyCutoffMulSectionLe
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.CutEnergy

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem wdb_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) : ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K := by
  set e := A.chart (C.idx a)
  have hg : ContDiffOn ℝ ∞ (fun w => ((χ (e.symm w) : ℝ) : ℂ)) e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ (C.idx a))
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
    hg.fderiv_of_isOpen e.open_target (by simp)
  have hc : ContinuousOn (fun v => ∑ j, ‖wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ)) v‖ ^ 2)
      e.target := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    have : ContDiffOn ℝ ∞ (wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
      ((hd.clm_apply contDiffOn_const).add
        (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2
    exact (this.continuousOn.norm).pow 2
  obtain ⟨K, hK⟩ := (isCompact_closedBall (C.c a) (C.r a)).exists_bound_of_continuousOn
    (hc.mono (C.sub a))
  refine ⟨max K 0, le_max_right _ _, fun v hv => ?_⟩
  have := hK v hv
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _))

theorem pt_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K)
    (la : La) (W Z : Set Y) (h : ι → Y → ℂ) (hW : IsOpen W) (hsupp : tsupport χ ⊆ W)
    (hsec : A.IsSecOn (A.kap + la) W h)
    (hZ : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) (v : V n) (hv : v ∈ ball (C.c a) (C.r a)) :
    ENNReal.ofReal ((∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) (C.idx a) ∘
        (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal K * ((Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y))
          ((A.chart (C.idx a)).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
  set i := C.idx a
  set e := A.chart i
  set y := e.symm v
  set g : V n → ℂ := fun w => ((χ (e.symm w) : ℝ) : ℂ)
  have hvt : v ∈ e.target := C.sub a (ball_subset_closedBall hv)
  have hys : y ∈ e.source := e.map_target hvt
  have hgs : ContDiffOn ℝ ∞ g e.target := Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ i)
  have hgd : DifferentiableAt ℝ g v :=
    (hgs.differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hvt)

  have hzero : y ∉ Z ∩ W → ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = 0 := by
    intro hy j
    by_cases hyW : y ∈ W
    · have hyZ : y ∉ Z := fun hz => hy ⟨hz, hyW⟩
      have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hyW⟩
      have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
        (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
      have hg0 : wdb n j g v = 0 := by
        have hev : g =ᶠ[𝓝 v] fun _ => ((χ y : ℝ) : ℂ) := by
          have := (e.continuousAt_symm hvt).eventually (hZ y hyZ)
          filter_upwards [this] with w hw
          simp only [g]; rw [hw]
        rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
        exact wdb_of_differentiableAt (differentiableAt_const _)
      have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
        rfl
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH, hg0]
      ring
    · have hyt : y ∉ tsupport χ := fun ht => hyW (hsupp ht)
      have h0 := (notMem_tsupport_iff_eventuallyEq.mp hyt)
      have hev : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        have := (e.continuousAt_symm hvt).eventually h0
        filter_upwards [this] with w hw
        simp only [Function.comp_apply, Pi.zero_apply] at hw ⊢
        rw [hw]; simp
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
      exact wdb_of_differentiableAt (differentiableAt_const _)
  by_cases hy : y ∈ Z ∩ W
  · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
    have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hy.2⟩
    have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
      (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
    have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
      rfl
    have hw : ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = wdb n j g v * h i y := by
      intro j
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH]
      simp [y]
    have hsum : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) =
        ‖h i y‖ ^ 2 * ∑ j, ‖wdb n j g v‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw j, norm_mul, mul_pow]; ring
    have hnsq := api_nsq_eq A hsec hys hy.2
    rw [A.ph_add _ _ i y hys] at hnsq
    have hexp : Real.exp (-A.ph la i y) =
        Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul (by unfold WeightedAtlas.nsq; positivity),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsum, ← hnsq, hexp]
    have hS := hK v (ball_subset_closedBall hv)
    have h1 : 0 ≤ ‖h i y‖ ^ 2 * (Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
        Real.exp (A.ph A.kap i y)) := by positivity
    calc ‖h i y‖ ^ 2 * (∑ j, ‖wdb n j g v‖ ^ 2) *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))
        = (∑ j, ‖wdb n j g v‖ ^ 2) * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) := by ring
      _ ≤ K * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_right hS h1
      _ = K * (‖h i y‖ ^ 2 * Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
          Real.exp (A.ph A.kap i y)) := by ring
  · have : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hzero hy j]; simp
    rw [this, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

end

end GlobalTheory.CutEnergy

namespace GlobalTheory.CutEnergy

theorem dbarEnergy_cutoff_mul_section_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A C χ hχ
  choose K hK0 hK using fun a => wdb_bound A C χ hχ a
  refine ⟨∑ a, K a, Finset.sum_nonneg fun a _ => hK0 a, ?_⟩
  intro la W Z h hW hsupp hsec hZm hZ
  set G : Y → ℝ≥0∞ := (Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) with hGdef
  have hGm : Measurable G := by
    classical
    have h1 : Measurable (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) := by
      rw [← Set.piecewise_eq_indicator]
      exact ContinuousOn.measurable_piecewise
        (ENNReal.continuous_ofReal.comp_continuousOn (api_nsq_contOn A hW hsec))
        continuousOn_const hW.measurableSet
    have : G = Z.indicator (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) :=
      (Set.indicator_indicator _ _ _).symm
    rw [this]; exact h1.indicator hZm
  have hint : ∫⁻ y, G y ∂A.mu = ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu :=
    lintegral_indicator (hZm.inter hW.measurableSet) _
  rw [← hint, ENNReal.ofReal_sum_of_nonneg (fun a _ => hK0 a), Finset.sum_mul]
  unfold n1
  refine Finset.sum_le_sum fun a _ => ?_
  calc _ ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (K a) *
          (G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
        setLIntegral_mono' measurableSet_ball fun v hv =>
          pt_bound A C χ hχ a (K a) (hK0 a) (hK a) la W Z h hW hsupp hsec hZ v hv
    _ = ENNReal.ofReal (K a) * ∫⁻ v in ball (C.c a) (C.r a), G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
          gcongr
          exact A.aap_lintegral_chart_le _ G hGm _ (ball_subset_closedBall.trans (C.sub a))

end GlobalTheory.CutEnergy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGlueSectionByPartitionEq
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem glue_wdb_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  intro n Y _ _ _ _ _ ι La _ A C la u i v w j hu hv
  have hopen : IsOpen (A.chart i).target := (A.chart i).open_target
  have hchi : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v := by
    intro a
    have h1 : ContDiffOn ℝ ∞ (C.chi a ∘ (A.chart i).symm) (A.chart i).target := C.smooth a i
    have h2 : DifferentiableAt ℝ (C.chi a ∘ (A.chart i).symm) v :=
      (h1.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)
    exact ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal h2
  have key : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v ∧
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v =
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v *
        (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
          u a (A.chart (C.idx a) ((A.chart i).symm v))) := by
    intro a
    by_cases hs : (A.chart i).symm v ∈ tsupport (C.chi a)
    · have hsrc := (C.supp a hs).1
      have hball : A.chart (C.idx a) ((A.chart i).symm v) ∈ ball (C.c a) (C.r a) := (C.supp a hs).2
      have hovl : IsOpen (ovl A.chart i (C.idx a)) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
      have hmem : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hsrc⟩
      have hg : DifferentiableAt ℂ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_g _ i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have htr : DifferentiableAt ℂ (A.chart (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_trans i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have hua : DifferentiableAt ℂ (u a) (A.chart (C.idx a) ((A.chart i).symm v)) :=
        (hu a).differentiableAt (isOpen_ball.mem_nhds hball)
      have hh : DifferentiableAt ℂ (fun x => A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) v :=
        hg.mul (hua.comp v htr)
      have heq : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =
          (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x)))) := by
        funext x; ring
      rw [heq]
      refine ⟨(hchi a).mul (hh.restrictScalars ℝ), ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_mul (hchi a) (hh.restrictScalars ℝ),
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt hh]
      ring
    · have hn : (A.chart i).symm ⁻¹' (tsupport (C.chi a))ᶜ ∈ 𝓝 v :=
        ((A.chart i).continuousAt_symm hv).preimage_mem_nhds
          ((isClosed_tsupport _).isOpen_compl.mem_nhds hs)
      have hz : ∀ᶠ x in 𝓝 v, C.chi a ((A.chart i).symm x) = 0 :=
        Filter.mem_of_superset hn fun x hx => image_eq_zero_of_notMem_tsupport hx
      have hf0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hc0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hw0 : wdb n j (fun _ : V n => (0 : ℂ)) v = 0 :=
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
      refine ⟨(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hf0, ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hf0, ReciprocityTheory.L2DbarEstimates.wdb_congr hc0, hw0, zero_mul]
  have hglue : glue C la u i ∘ (A.chart i).symm = fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x)) := by
    funext x; rfl
  have hone : (fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ)) = fun _ : V n => (1 : ℂ) := by
    funext x; rw [← Complex.ofReal_sum, C.sum_one]; simp
  have hsum0 : ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
    rw [← ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => hchi a), hone]
    exact ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
  rw [hglue, ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => (key a).1)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun a _ => (key a).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseNonvanishingSetOfNeZeroOnComponents
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem nz_dense_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ →
    (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) →
    Dense (nz A τ) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ T hs hT hP
  set Zs : Set Y := {y | τ (A.pick y) y = 0} with hZs
  have hc : (nz A τ)ᶜ = Zs := by
    ext y; simp [nz, Zs]

  have toI : ∀ i x, x ∈ (A.chart i).source → τ (A.pick x) x = 0 → τ i x = 0 := by
    intro i x hx h0
    rw [hs.2 i (A.pick x) x (Set.mem_univ _) hx (A.mem_pick x), h0, mul_zero]
  have toP : ∀ i x, x ∈ (A.chart i).source → τ i x = 0 → τ (A.pick x) x = 0 := by
    intro i x hx h0
    rw [hs.2 (A.pick x) i x (Set.mem_univ _) (A.mem_pick x) hx, h0, mul_zero]
  set Z := interior Zs with hZ
  have hZo : IsOpen Z := isOpen_interior
  have hZc : IsClosed Z := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    set i := A.pick y
    set e := A.chart i
    have hyv : e y ∈ e.target := e.map_source (A.mem_pick y)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) hyv
    set W : Set Y := e.source ∩ e ⁻¹' ball (e y) r
    have hWo : IsOpen W := e.isOpen_inter_preimage isOpen_ball
    have hyW : y ∈ W := ⟨A.mem_pick y, by exact Set.mem_preimage.mpr (mem_ball_self hr)⟩
    obtain ⟨x, hxW, hxZ⟩ := (mem_closure_iff.mp hy) W hWo hyW
    set F : V n → ℂ := τ i ∘ e.symm
    have hF : DifferentiableOn ℂ F (ball (e y) r) := by
      have := hs.1 i
      refine this.mono ?_
      intro w hw; exact ⟨hball hw, Set.mem_univ _⟩
    have hxs : e x ∈ ball (e y) r := hxW.2
    have hev : F =ᶠ[𝓝 (e x)] 0 := by
      have hxt : e x ∈ e.target := e.map_source hxW.1
      have h1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ Z := by
        have hca : ContinuousAt e.symm (e x) := e.continuousAt_symm hxt
        have : e.symm (e x) = x := e.left_inv hxW.1
        refine hca.preimage_mem_nhds ?_
        rw [this]; exact hZo.mem_nhds hxZ
      have h2 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target := e.open_target.mem_nhds hxt
      filter_upwards [h1, h2] with w hw1 hw2
      have hsrc : e.symm w ∈ e.source := e.map_target hw2
      exact toI i _ hsrc (interior_subset (s := Zs) hw1)
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball (e y) r) F (e x) isOpen_ball (convex_ball _ _) hF hxs hev
    have hWZs : W ⊆ Zs := by
      intro z hz
      have h0 : F (e z) = 0 := hEq hz.2
      have : τ i z = 0 := by
        simpa [F, e.left_inv hz.1] using h0
      exact toP i z hz.1 this
    exact interior_maximal hWZs hWo hyW
  have hempty : Z = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨P, hPT, hPc⟩ := hT y
    have hsub := (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ hy)
    exact hP P hPT (interior_subset (s := Zs) (hsub hPc))
  have hd := interior_eq_empty_iff_dense_compl.mp hempty
  rw [← hc, compl_compl] at hd
  exact hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish (δ : DividedPowers J) (a : B) (N : ℕ)
    (h : ∀ n, N ≤ n → δ.dpow n a = 0) :
    _root_.GlobalTheory.Cris.dpExp δ a = ∑ n ∈ Finset.range N, δ.dpow n a := by
  unfold _root_.GlobalTheory.Cris.dpExp
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  exact hn (h n (not_lt.mp hlt))


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.IsNilDP.dpExp_add_eq_mul {δ : DividedPowers J}
    (h : _root_.GlobalTheory.Cris.IsNilDP δ) {a b : B} (ha : a ∈ J) (hb : b ∈ J) :
    _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b := by
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ x ∈ J, ∀ n, N ≤ n → δ.dpow n x = 0 := by
    intro x hx n hn
    simpa using hN [(n, x)] (by simpa using hx) (by simpa using hn)
  have hpair : ∀ i j, N ≤ i + j → δ.dpow i a * δ.dpow j b = 0 := by
    intro i j hij
    simpa using hN [(i, a), (j, b)] (by simp [ha, hb]) (by simpa using hij)
  let F : ℕ × ℕ → B := fun p => δ.dpow p.1 a * δ.dpow p.2 b
  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ (a + b) N (hvan _ (J.add_mem ha hb)),
    _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N (hvan a ha), _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ b N (hvan b hb),
    Finset.sum_mul_sum, ← Finset.sum_product' (f := fun i j => δ.dpow i a * δ.dpow j b)]
  have hfilter : ∑ p ∈ Finset.range N ×ˢ Finset.range N with p.1 + p.2 < N, F p =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, F p := by
    refine Finset.sum_filter_of_ne fun p _ hp => ?_
    by_contra hlt
    exact hp (hpair p.1 p.2 (not_lt.mp hlt))
  rw [← hfilter, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2) (fun p hp => by simpa using (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [δ.dpow_add ha hb]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨i, j⟩
  simp only [Finset.mem_range] at hn
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  omega


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.dpExp_add_and_natural (B B' : Type) [CommRing B] [CommRing B'] (J : Ideal B) (J' : Ideal B')
    (δ : DividedPowers J) (δ' : DividedPowers J') (h : _root_.GlobalTheory.Cris.IsNilDP δ) :
    (∀ a ∈ J, ∀ b ∈ J, _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b) ∧
      (∀ f : B →+* B', IsDPMorphism δ δ' f → ∀ a ∈ J,
        f (_root_.GlobalTheory.Cris.dpExp δ a) = _root_.GlobalTheory.Cris.dpExp δ' (f a)) := by
  refine ⟨fun a ha b hb => h.dpExp_add_eq_mul ha hb, fun f hf a ha => ?_⟩
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ n, N ≤ n → δ.dpow n a = 0 := by
    intro n hn
    simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  have hvan' : ∀ n, N ≤ n → δ'.dpow n (f a) = 0 := by
    intro n hn
    rw [← hf.map_dpow ha, hvan n hn, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N hvan, _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ' (f a) N hvan',
    map_sum]
  exact Finset.sum_congr rfl fun n _ => hf.map_dpow ha

end GlobalTheory.Cris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassTorsionConjTransport
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.Transp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT c₀ c₁ τ₀ τ₁ h₀ h₁ ω₀ ω₁ hω₀ hω₁
  subst hω₀ hω₁
  have hT' := hT
  obtain ⟨hΩ₀, hΩ₁, -, -, -, hg₂, hg₃, hwp⟩ := hT'
  have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have hE := map_eisenstein_div_period g Λ₀ Λ₁ c₀ c₁ Ω₀ Ω₁ τ₀ τ₁ h₀ h₁ hg₂ hg₃
  have hs₀ := _root_.GlobalTheory.WpFam.TauVal.main Λ₀ c₀ Ω₀ τ₀ h₀
  have hs₁ := _root_.GlobalTheory.WpFam.TauVal.main Λ₁ c₁ Ω₁ τ₁ h₁
  have hs := _root_.GlobalTheory.NormSqOfSquareEqNeg.main K d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  refine ⟨div_ne_zero (mul_ne_zero hΩ₀ h₀.1) h2πi, div_ne_zero (mul_ne_zero hΩ₁ h₁.1) h2πi,
    hE.1, hE.2, ?_, ?_⟩
  · rw [hs₀.1, hs₁.1, hs]
  · intro N _
    obtain ⟨A, hA⟩ := _root_.GlobalTheory.WpFam.exists_torsion_matrix K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT c₀ c₁ τ₀ τ₁ h₀ h₁ N
    refine ⟨A, hA, fun x => ?_⟩
    rw [(hs₀.2 N x).1, (hs₀.2 N x).2, (hs₁.2 N (vmul x A)).1, (hs₁.2 N (vmul x A)).2]
    by_cases hx : x = 0
    · have hv : vmul x A = 0 := ((GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x A).2 hx
      have ht : ∀ τ : ℍ, tors N τ 0 = 0 := by intro τ; simp [tors]
      rw [hv, hx, ht, ht, mul_zero, mul_zero]
      simp [PeriodPair.weierstrassP_zero, PeriodPair.derivWeierstrassP_zero]
    · obtain ⟨k, k', hk, hk', htr⟩ := hA x
      have hnot : ι k ∉ Λ₀.lattice := by
        rw [hk, ((_root_.GlobalTheory.WpFam.homogeneity_of_isTauOf Λ₀ c₀ τ₀ h₀).1 _), ((GlobalTheory.WpFam.TorsMem.main N τ₀).2.2.1 x)]
        exact hx
      rw [← hk, ← hk']
      exact hwp k k' hnot htr

end GlobalTheory.WpFam.Transp
end

