module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SummableNinePowMulInvSqSucc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
section
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma exists_compact_exhaustion_with_bumps {V : Type} [MetricSpace V] [ProperSpace V]
    {G : Set V} (hG : IsOpen G) :
    ∃ (K : ℕ → Set V) (f : ℕ → C(V, ℝ)), Monotone K ∧ ⋃ n, K n = G ∧
      ∀ n, IsCompact (K n) ∧ EqOn (f n) 1 (K n) ∧ IsCompact (tsupport (f n)) ∧
        tsupport (f n) ⊆ G ∧ ∀ v, f n v ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  let E := CompactExhaustion.choice V
  let K : ℕ → Set V := fun n => F n ∩ E n
  have hKm : Monotone K := fun a b hab => inter_subset_inter (hFm hab) (E.subset hab)
  have hKU : ⋃ n, K n = G := by
    apply Subset.antisymm
    · exact iUnion_subset fun n => inter_subset_left.trans (hFG n)
    · intro x hx
      rw [← hFU] at hx
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      obtain ⟨b, hb⟩ := E.exists_mem x
      exact mem_iUnion.2 ⟨max a b, hFm (le_max_left a b) ha, E.subset (le_max_right a b) hb⟩
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).inter_left (hFc n)
  choose f hf1 hfc hfG hf01 using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hKc n) hG
      (inter_subset_left.trans (hFG n))
  exact ⟨K, f, hKm, hKU, fun n => ⟨hKc n, hf1 n, hfc n, hfG n, hf01 n⟩⟩

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma measure_le_lintegral_of_eqOn_one {V : Type} [MeasurableSpace V] (μ : Measure V)
    {K : Set V} (hK : MeasurableSet K) {g : V → ℝ} (hg : EqOn g 1 K) :
    μ K ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂μ := by
  rw [← lintegral_indicator_one hK]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [indicator_of_mem hv, hg hv]
  · simp [indicator_of_notMem hv]

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma measure_isOpen_le_of_lintegral_le {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) {G : Set V} (hG : IsOpen G)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ G → (∀ v, 0 ≤ φ v) →
      ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m G ≤ m' G := by
  obtain ⟨K, f, hKm, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hG
  have hGK : m G = ⨆ n, m (K n) := by rw [← hKm.measure_iUnion, hKU]
  rw [hGK]
  refine iSup_le fun n => ?_
  obtain ⟨hKc, hf1, hfc, hfG, hf01⟩ := hKf n
  calc m (K n) ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m :=
        measure_le_lintegral_of_eqOn_one m hKc.isClosed.measurableSet hf1
    _ ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m' :=
        h (f n) (f n).continuous hfc hfG fun v => (hf01 v).1
    _ ≤ ∫⁻ v, G.indicator 1 v ∂m' := by
        refine lintegral_mono fun v => ?_
        by_cases hv : v ∈ G
        · simp [indicator_of_mem hv, (hf01 v).2]
        · have : f n v = 0 := image_eq_zero_of_notMem_tsupport fun h' => hv (hfG h')
          simp [this]
    _ = m' G := lintegral_indicator_one hG.measurableSet


open MeasureTheory Set Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) (O : Set V) (hO : IsOpen O)
    (hm : m Oᶜ = 0) (hm' : m' Oᶜ = 0)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ v, 0 ≤ φ v) →
      Integrable φ m ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂m = ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m = m' := by
  have hopen : ∀ G : Set V, IsOpen G → G ⊆ O → m G = m' G := fun G hG hGO =>
    le_antisymm
      (measure_isOpen_le_of_lintegral_le m m' hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.le)
      (measure_isOpen_le_of_lintegral_le m' m hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.ge)
  obtain ⟨K, f, -, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hO
  let W : Option ℕ → Set V := fun i => i.elim Oᶜ fun n => {v | 0 < f n v}
  have hWU : ⋃ i, W i = univ := by
    refine eq_univ_of_forall fun v => ?_
    by_cases hv : v ∈ O
    · rw [← hKU] at hv
      obtain ⟨n, hn⟩ := mem_iUnion.1 hv
      exact mem_iUnion.2 ⟨some n, show 0 < f n v by simp [(hKf n).2.1 hn]⟩
    · exact mem_iUnion.2 ⟨none, hv⟩
  rw [Measure.ext_iff_of_iUnion_eq_univ hWU]
  rintro (_ | n)
  · simp [W, Measure.restrict_eq_zero.2 hm, Measure.restrict_eq_zero.2 hm']
  · obtain ⟨-, -, hfc, hfO, -⟩ := hKf n
    have hWo : IsOpen {v | 0 < f n v} := isOpen_lt continuous_const (f n).continuous
    have hsub : {v | 0 < f n v} ⊆ tsupport (f n) := fun v hv =>
      subset_tsupport _ (ne_of_gt (show 0 < f n v from hv))
    have hWO : {v | 0 < f n v} ⊆ O := hsub.trans hfO
    obtain ⟨g, hg1, hgc, hgO, hg01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hfc hO hfO
    have hfin : m {v | 0 < f n v} < ∞ :=
      (measure_mono hsub).trans_lt <|
        (measure_le_lintegral_of_eqOn_one m hfc.isClosed.measurableSet hg1).trans_lt
          (h g g.continuous hgc hgO fun v => (hg01 v).1).1.lintegral_lt_top
    haveI : IsFiniteMeasure (m.restrict {v | 0 < f n v}) := isFiniteMeasure_restrict.2 hfin.ne
    show m.restrict {v | 0 < f n v} = m'.restrict {v | 0 < f n v}
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
      exact hopen _ (hs.inter hWo) (inter_subset_right.trans hWO)
    · simpa using hopen _ hWo hWO


open MeasureTheory Set Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.IsFibreFamily_lintegral_preimage {V : Type} [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V} {f : V → ℝ} {O U : Set V} {B : Set ℝ}
    {fib : ℝ → Measure V}
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U)
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ v in O, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h
  obtain ⟨hfib, hint, -⟩ := h
  have hψ : Measurable ((f ⁻¹' S).indicator φ) := hφ.indicator (hf hS)
  have hsupp : Function.support ((f ⁻¹' S).indicator φ) ⊆ O := by
    intro v hv
    by_contra hvO
    exact hv (by simp [indicator, hs v hvO])
  rw [setLIntegral_eq_of_support_subset hsupp,
    ← setLIntegral_eq_of_support_subset (hsupp.trans hU), hint _ hψ, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ v ∂(fib b), f v = b := by
    refine ae_iff.2 (measure_mono_null ?_ (hfib b))
    intro v hv hv'
    exact hv hv'.1
  by_cases hb : b ∈ S
  · rw [indicator_of_mem hb]
    exact lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])
  · rw [indicator_of_notMem hb]
    exact (lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])).trans
      lintegral_zero

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma le_of_setLIntegral_eq_near {g g' : ℝ → ℝ} {β : ℝ} {W : Set ℝ} (hW : W ∈ 𝓝 β)
    (hg : ContinuousAt g β) (hg' : ContinuousAt g' β) (hg0 : 0 ≤ g' β)
    (h : ∀ S ⊆ W, MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (g b) = ∫⁻ b in S, ENNReal.ofReal (g' b)) :
    g β ≤ g' β := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c₁, h₁, h₂⟩ := exists_between hlt
  obtain ⟨c₂, h₃, h₄⟩ := exists_between h₂
  have e₁ : ∀ᶠ b in 𝓝 β, g' b < c₁ := hg'.eventually (gt_mem_nhds h₁)
  have e₂ : ∀ᶠ b in 𝓝 β, c₂ < g b := hg.eventually (lt_mem_nhds h₄)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hW (e₁.and e₂))
  have hS : MeasurableSet (Metric.ball β ε) := measurableSet_ball
  have hpos : volume (Metric.ball β ε) ≠ 0 := (Metric.measure_ball_pos volume β hε).ne'
  have hfin : volume (Metric.ball β ε) ≠ ∞ := measure_ball_lt_top.ne
  have low : ENNReal.ofReal c₂ * volume (Metric.ball β ε) ≤
      ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g b) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.2.le))
  have up : ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g' b) ≤
      ENNReal.ofReal c₁ * volume (Metric.ball β ε) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.1.le))
  have key := low.trans ((h _ (fun b hb => (hball hb).1) hS).le.trans up)
  have key' : ENNReal.ofReal c₂ ≤ ENNReal.ofReal c₁ := (ENNReal.mul_le_mul_iff_left hpos hfin).1 key
  rw [ENNReal.ofReal_le_ofReal_iff (hg0.trans h₁.le)] at key'
  exact absurd key' (not_le.2 h₃)


open MeasureTheory Set Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.IsFibreFamily_eq_at {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (f : V → ℝ)
    (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ)
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U) (hU' : O ⊆ U') (hβ : f ⁻¹' {β} ⊆ O)
    (hB : IsOpen B) (hB' : IsOpen B') (hβB : β ∈ B) (hβB' : β ∈ B')
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (h' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib') : fib β = fib' β := by
  have hdens := fun (S : Set ℝ) (hS : MeasurableSet S) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
      (hs : ∀ v, v ∉ O → φ v = 0) =>
    (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU h φ hφ hs S hS).symm.trans
      (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU' h' φ hφ hs S hS)
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h h'
  obtain ⟨hfib, -, hcts⟩ := h
  obtain ⟨hfib', -, hcts'⟩ := h'
  have hnull : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U)ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  have hnull' : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U')ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  refine _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (measure_mono_null hnull (hfib β))
    (measure_mono_null hnull' (hfib' β)) fun φ hφc hφs hφO hφ0 => ?_
  obtain ⟨hi, hc⟩ := hcts φ hφc hφs (hφO.trans hU)
  obtain ⟨hi', hc'⟩ := hcts' φ hφc hφs (hφO.trans hU')
  refine ⟨hi β hβB, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβB) (Filter.Eventually.of_forall hφ0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβB') (Filter.Eventually.of_forall hφ0)]
  have hW : B ∩ B' ∈ 𝓝 β := Filter.inter_mem (hB.mem_nhds hβB) (hB'.mem_nhds hβB')
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) := hφc.measurable.ennreal_ofReal
  have hφz : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
    rw [image_eq_zero_of_notMem_tsupport fun h'' => hv (hφO h'')]
    simp
  have hset : ∀ S ⊆ B ∩ B', MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib b) =
        ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib' b) := by
    intro S hSW hS
    rw [setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi b (hSW hb).1) (Filter.Eventually.of_forall hφ0),
      setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi' b (hSW hb).2) (Filter.Eventually.of_forall hφ0)]
    exact hdens S hS _ hφm hφz
  have hca := hc.continuousAt (hB.mem_nhds hβB)
  have hca' := hc'.continuousAt (hB'.mem_nhds hβB')
  congr 1
  exact le_antisymm
    (le_of_setLIntegral_eq_near hW hca hca' (integral_nonneg hφ0) hset)
    (le_of_setLIntegral_eq_near hW hca' hca (integral_nonneg hφ0) fun S hSW hS =>
      (hset S hSW hS).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LWide

theorem disc (r R : ℝ) (hr : 0 < r) (hrR : r < R) (hR : R < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (a M : ℝ), 0 < a → Differentiable ℂ F → F c ≠ 0 →
      (∀ z, ‖z - c‖ ≤ a → ‖F z‖ ≤ M) →
      {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖)) ∧
      ∀ s : ℂ, ‖s - c‖ ≤ r * a → F s ≠ 0 →
        a * ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0},
          (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by
  obtain ⟨C, hC, H⟩ := LogDerivZeros.main r R hr hrR hR
  refine ⟨C, hC, fun F c a M ha hF hc hM => ?_⟩
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set φ : ℂ → ℂ := fun z => c + a * z with hφ
  have hφn : ∀ z, ‖φ z - c‖ = a * ‖z‖ := fun z => by
    simp [hφ, abs_of_pos ha]
  have hφd : ∀ z, HasDerivAt φ a z := fun z => by
    simpa [hφ] using ((hasDerivAt_id z).const_mul (a : ℂ)).const_add c
  have hφa : ∀ z, AnalyticAt ℂ φ z := fun z => by
    simp only [hφ]; fun_prop
  have hφ0 : φ 0 = c := by simp [hφ]
  have hinj : Function.Injective φ := fun x y h => by
    simpa [hφ, hac] using h
  have hsurj : ∀ w, φ ((w - c) / a) = w := fun w => by
    simp only [hφ]; field_simp; ring
  obtain ⟨⟨h1, h2⟩, h3⟩ := H (F ∘ φ) M
    (fun z _ => (hF.analyticAt _).comp (hφa z)) (by simpa [hφ0] using hc)
    (fun z hz => hM _ (by
      rw [hφn]; exact mul_le_of_le_one_right ha.le (by simpa using hz)))
  have hset : {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0} = φ '' {w : ℂ | ‖w‖ ≤ R ∧ (F ∘ φ) w = 0} := by
    ext w
    constructor
    · rintro ⟨hw, hw0⟩
      refine ⟨(w - c) / a, ⟨?_, by simpa [hsurj] using hw0⟩, hsurj w⟩
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, div_le_iff₀ ha]
      exact hw
    · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
      refine ⟨?_, hz0⟩
      rw [hφn, mul_comm]
      gcongr
  have hord : ∀ z, analyticOrderNatAt (F ∘ φ) z = analyticOrderNatAt F (φ z) := fun z => by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_comp_of_deriv_ne_zero (hφa z) (by rw [(hφd z).deriv]; exact hac)]
  simp only [hord, Function.comp_apply (f := F) (g := φ) (x := 0), hφ0] at h2 h3
  rw [hset]
  refine ⟨h1.image _, ?_, fun s hs hs0 => ?_⟩
  · rw [finsum_mem_image hinj.injOn]
    exact h2
  · obtain ⟨z, rfl⟩ : ∃ z, φ z = s := ⟨_, hsurj s⟩
    rw [finsum_mem_image hinj.injOn]
    rw [hφn, mul_comm] at hs
    have h4 := h3 z (le_of_mul_le_mul_right hs ha) hs0
    refine le_trans (le_of_eq ?_) h4
    have hd : deriv (F ∘ φ) z = deriv F (φ z) * a :=
      ((hF (φ z)).hasDerivAt.comp z (hφd z)).deriv
    rw [hd, finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h1]
    conv_lhs => rw [← Real.norm_of_nonneg ha.le, ← Complex.norm_real, ← norm_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · simp only [Function.comp_apply]; ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      have : φ z - φ w = a * (z - w) := by simp only [hφ]; ring
      rw [this, ← mul_div_assoc, mul_div_mul_left _ _ hac]

theorem logDeriv_LFunction_strip : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℝ)) ≤ C * Real.log (q * (|s.im| + 2)) ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|s.im| + 2)) := by
  obtain ⟨C, hC, H⟩ := disc (4 / 5) (14 / 15) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B, hB, G⟩ := norm_LFunction_le_poly_left
  refine ⟨C * (2 * (1 + |Real.log (512 * B)|) + 4), by positivity, ?_⟩
  intro q _ χ hχ s hs1 hs2 hs0
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set c : ℂ := 2 + s.im * I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcn : ‖c‖ ≤ 2 + |s.im| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp
  have hlow : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have := LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    linarith
  have ht := abs_nonneg s.im
  set X : ℝ := q * (|s.im| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hlX : 1 / 2 ≤ Real.log X := by
    have := Real.log_le_log (by norm_num) hX2
    linarith [Real.log_two_gt_d9]
  have hpos : 0 < ‖LFunction χ c‖ := by linarith
  obtain ⟨h1, h2, h3⟩ := H (LFunction χ) c (15 / 4) (256 * B * X ^ 4) (by norm_num)
    (differentiable_LFunction hχ) (norm_pos_iff.1 hpos) (fun z hz => by
      have hre : -(7 / 4 : ℝ) ≤ z.re := by
        have := (abs_le.1 ((Complex.abs_re_le_norm (z - c)).trans hz)).1
        rw [sub_re, hcre] at this
        linarith
      refine (G q χ hχ z hre).trans ?_
      have hzn : ‖z‖ + 2 ≤ 4 * (|s.im| + 2) := by
        have := norm_le_norm_sub_add z c
        linarith
      calc B * (q : ℝ) ^ 4 * (‖z‖ + 2) ^ 4 ≤ B * (q : ℝ) ^ 4 * (4 * (|s.im| + 2)) ^ 4 := by gcongr
        _ = _ := by rw [hX]; ring)
  have e : (14 / 15 : ℝ) * (15 / 4) = 7 / 2 := by norm_num
  rw [e] at h1 h2 h3
  have hsc : ‖s - c‖ ≤ 4 / 5 * (15 / 4) := by
    have : s - c = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h4 := h3 s hsc hs0
  have hlog : Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖) ≤ Real.log (512 * B) + 4 * Real.log X := by
    have hX0 : 0 < X := by linarith
    have : 256 * B * X ^ 4 / ‖LFunction χ c‖ ≤ 512 * B * X ^ 4 := by
      rw [div_le_iff₀ hpos]
      have : 0 < B * X ^ 4 := by positivity
      nlinarith
    refine (Real.log_le_log (by positivity) this).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hfin : C * (1 + Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖))
      ≤ C * (2 * (1 + |Real.log (512 * B)|) + 4) * Real.log X := by
    rw [mul_assoc C]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have h5 := le_abs_self (Real.log (512 * B))
    have h6 := abs_nonneg (Real.log (512 * B))
    nlinarith
  refine ⟨h1, h2.trans hfin, le_trans ?_ (h4.trans hfin)⟩
  exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)

end GlobalTheory.LWide
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRiemannZetaSubPartialSumLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open Set

namespace GlobalTheory.ZetaPartialSum
open GlobalTheory.ZetaHalfPlane

noncomputable def tailInt (s : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi a, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

lemma norm_tailInt_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖tailInt s a‖ ≤ a ^ (-s.re) / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖tailInt s a‖ ≤ ∫ t in Ioi a, t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h ha) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun t ht => ?_
        have ht0 : 0 < t := lt_trans ha ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)
    _ = a ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt h ha,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]

lemma piece {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    s * ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = (M : ℂ) ^ (1 - s) / (s - 1) - ((M : ℂ) + 1) ^ (1 - s) / (s - 1)
        - ((M : ℂ) + 1) ^ (-s) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hle : (M : ℝ) ≤ M + 1 := by linarith
  have hmem : (0 : ℝ) ∉ uIcc (M : ℝ) (M + 1) := by
    rw [uIcc_of_le hle]
    intro h
    linarith [h.1]
  have e : ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = ∫ t in (M : ℝ)..(M + 1), ((t : ℂ) ^ (-s) - (M : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := lt_trans hM0 ht.1
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    have e1 : (t : ℂ) ^ (-s) = t * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = 1 + -(s + 1) by ring, cpow_add _ _ htc, cpow_one]
    have e2 : ⌊t⌋ = (M : ℤ) := by
      rw [Int.floor_eq_iff]
      exact ⟨by simpa using ht.1.le, by simpa using ht.2⟩
    have e3 : Int.fract t = t - M := by
      rw [Int.fract, e2]; simp
    rw [e1, e3]
    push_cast
    ring
  have i1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have i2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have n1 : -s ≠ -1 := fun h => hs1 (neg_injective h)
  have n2 : -(s + 1) ≠ -1 := fun h => hs0 (by linear_combination -h)
  rw [e, intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨n1, hmem⟩), integral_cpow (Or.inr ⟨n2, hmem⟩)]
  push_cast
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hMc1 : (M : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
  have a1 : (M : ℂ) ^ (1 - s) = M * (M : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc, cpow_one]
  have a2 : ((M : ℂ) + 1) ^ (1 - s) = (M + 1) * ((M : ℂ) + 1) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc1, cpow_one]
  rw [show -s + 1 = 1 - s by ring, show -(s + 1) + 1 = -s by ring, a1, a2]
  have hs1'' : 1 - s ≠ 0 := sub_ne_zero.2 hs1.symm
  field_simp
  ring

theorem zeta_eq_sum {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) + (M : ℂ) ^ (1 - s) / (s - 1)
      - s * tailInt s M := by
  induction M, hM using Nat.le_induction with
  | base =>
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    rw [zeta_eq hs hs1]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow, tailInt, fractInt]
    field_simp
    ring
  | succ M hM ih =>
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hle : (M : ℝ) ≤ M + 1 := by linarith
    have hsplit : tailInt s M
        = (∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
          + tailInt s ((M : ℝ) + 1) := by
      unfold tailInt
      rw [← Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
      · exact (integrableOn_integrand hs).mono_set fun t ht => lt_of_le_of_lt hM1 ht.1
      · exact (integrableOn_integrand hs).mono_set fun t ht =>
          lt_of_le_of_lt (hM1.trans hle) ht
    rw [ih, Finset.sum_Icc_succ_top (by omega), hsplit, mul_add, piece hs hs1 hM]
    push_cast
    ring

theorem norm_zeta_sub_sum_le :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M →
      ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖
        ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  intro s hs hs1 M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have e : riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)
      = -(s * tailInt s M) := by
    rw [zeta_eq_sum hs hs1 hM]; ring
  rw [e, norm_neg, norm_mul, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_tailInt_le hs hM0) (norm_nonneg s)

end GlobalTheory.ZetaPartialSum
end

