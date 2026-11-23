module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoSublevelDensityProdMeasure
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.SublevelDensity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
private lemma mul_prod_sublevel_add_le_of_fst_sublevel_le {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] (m : Measure A) (m' : Measure A') (μ : Measure B) [SFinite m]
    [SFinite m'] [SFinite μ] (n : A → ℝ) (n' : A' → ℝ) (g : B → ℝ) (hn : Measurable n)
    (hn' : Measurable n') (hg : Measurable g) (hn0 : ∀ x, 0 ≤ n x) (hn0' : ∀ x, 0 ≤ n' x)
    (hg0 : ∀ y, 0 ≤ g y) (a b : ℝ≥0∞) (r : ℝ)
    (h : ∀ s, 0 < s → s ≤ r → a * m {x | n x < s} ≤ b * m' {x | n' x < s}) :
    a * (m.prod μ) {p | n p.1 + g p.2 < r} ≤ b * (m'.prod μ) {p | n' p.1 + g p.2 < r} := by
  have hS : MeasurableSet {p : A × B | n p.1 + g p.2 < r} :=
    measurableSet_lt ((hn.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  have hS' : MeasurableSet {p : A' × B | n' p.1 + g p.2 < r} :=
    measurableSet_lt ((hn'.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply_symm hS, Measure.prod_apply_symm hS']
  calc a * ∫⁻ y, m ((fun x => (x, y)) ⁻¹' {p : A × B | n p.1 + g p.2 < r}) ∂μ
      ≤ ∫⁻ y, a * m ((fun x => (x, y)) ⁻¹' {p : A × B | n p.1 + g p.2 < r}) ∂μ :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ y, b * m' ((fun x => (x, y)) ⁻¹' {p : A' × B | n' p.1 + g p.2 < r}) ∂μ := by
        refine lintegral_mono fun y => ?_
        simp only [Set.preimage_setOf_eq]
        by_cases hy : r ≤ g y
        · have e1 : {x | n x + g y < r} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0 x]
          have e2 : {x | n' x + g y < r} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0' x]
          rw [e1, e2]
          simp
        · push_neg at hy
          have e1 : {x | n x + g y < r} = {x | n x < r - g y} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hx <;> linarith
          have e2 : {x | n' x + g y < r} = {x | n' x < r - g y} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hx <;> linarith
          rw [e1, e2]
          exact h _ (by linarith) (by linarith [hg0 y])
    _ = b * ∫⁻ y, m' ((fun x => (x, y)) ⁻¹' {p : A' × B | n' p.1 + g p.2 < r}) ∂μ :=
        lintegral_const_mul _ (measurable_measure_prodMk_right hS')

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
private lemma mul_prod_sublevel_add_le_of_snd_sublevel_le {A B B' : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace B'] (μ : Measure A) (m : Measure B) (m' : Measure B') [SFinite m]
    [SFinite m'] (g : A → ℝ) (n : B → ℝ) (n' : B' → ℝ) (hg : Measurable g) (hn : Measurable n)
    (hn' : Measurable n') (hg0 : ∀ x, 0 ≤ g x) (hn0 : ∀ y, 0 ≤ n y) (hn0' : ∀ y, 0 ≤ n' y)
    (a b : ℝ≥0∞) (r : ℝ)
    (h : ∀ s, 0 < s → s ≤ r → a * m {y | n y < s} ≤ b * m' {y | n' y < s}) :
    a * (μ.prod m) {p | g p.1 + n p.2 < r} ≤ b * (μ.prod m') {p | g p.1 + n' p.2 < r} := by
  have hS : MeasurableSet {p : A × B | g p.1 + n p.2 < r} :=
    measurableSet_lt ((hg.comp measurable_fst).add (hn.comp measurable_snd)) measurable_const
  have hS' : MeasurableSet {p : A × B' | g p.1 + n' p.2 < r} :=
    measurableSet_lt ((hg.comp measurable_fst).add (hn'.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply hS, Measure.prod_apply hS']
  calc a * ∫⁻ x, m (Prod.mk x ⁻¹' {p : A × B | g p.1 + n p.2 < r}) ∂μ
      ≤ ∫⁻ x, a * m (Prod.mk x ⁻¹' {p : A × B | g p.1 + n p.2 < r}) ∂μ :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ x, b * m' (Prod.mk x ⁻¹' {p : A × B' | g p.1 + n' p.2 < r}) ∂μ := by
        refine lintegral_mono fun x => ?_
        simp only [Set.preimage_setOf_eq]
        by_cases hx : r ≤ g x
        · have e1 : {y | g x + n y < r} = ∅ := by
            ext y
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0 y]
          have e2 : {y | g x + n' y < r} = ∅ := by
            ext y
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0' y]
          rw [e1, e2]
          simp
        · push_neg at hx
          have e1 : {y | g x + n y < r} = {y | n y < r - g x} := by
            ext y
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hy <;> linarith
          have e2 : {y | g x + n' y < r} = {y | n' y < r - g x} := by
            ext y
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hy <;> linarith
          rw [e1, e2]
          exact h _ (by linarith) (by linarith [hg0 x])
    _ = b * ∫⁻ x, m' (Prod.mk x ⁻¹' {p : A × B' | g p.1 + n' p.2 < r}) ∂μ :=
        lintegral_const_mul _ (measurable_measure_prodMk_left hS')


open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
theorem _root_.GlobalTheory.SublevelDensity.tendsto_prod_density : ∀ (A₁ E₁ A₂ E₂ : Type) [MeasurableSpace A₁] [MeasurableSpace E₁] [MeasurableSpace A₂] [MeasurableSpace E₂] (m₁ : Measure A₁) (l₁ : Measure E₁) (m₂ : Measure A₂) (l₂ : Measure E₂) [SFinite m₁] [SFinite l₁] [SFinite m₂] [SFinite l₂] (n₁ : A₁ → ℝ) (N₁ : E₁ → ℝ) (n₂ : A₂ → ℝ) (N₂ : E₂ → ℝ) (c₁ c₂ : ℝ≥0∞), Measurable n₁ → Measurable N₁ → Measurable n₂ → Measurable N₂ → (∀ x, 0 ≤ n₁ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ n₂ x) → (∀ x, 0 ≤ N₂ x) → c₁ ≠ ⊤ → c₂ ≠ ⊤ → (∀ r : ℝ, 0 < r → l₁ {x | N₁ x < r} ≠ 0 ∧ l₁ {x | N₁ x < r} ≠ ⊤) → (∀ r : ℝ, 0 < r → l₂ {x | N₂ x < r} ≠ 0 ∧ l₂ {x | N₂ x < r} ≠ ⊤) → Tendsto (fun r : ℝ => m₁ {x | n₁ x < r} / l₁ {x | N₁ x < r}) (𝓝[>] 0) (𝓝 c₁) → Tendsto (fun r : ℝ => m₂ {x | n₂ x < r} / l₂ {x | N₂ x < r}) (𝓝[>] 0) (𝓝 c₂) → Tendsto (fun r : ℝ => (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} / (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
  intro A₁ E₁ A₂ E₂ _ _ _ _ m₁ l₁ m₂ l₂ _ _ _ _ n₁ N₁ n₂ N₂ c₁ c₂ hn₁ hN₁ hn₂ hN₂ hn₁0 hN₁0
    hn₂0 hN₂0 hc₁ hc₂ hl₁ hl₂ h₁ h₂
  have hG : ∀ r : ℝ, 0 < r → (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≠ 0 ∧
      (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≠ ⊤ := by
    intro r hr
    constructor
    · have hsub : {x | N₁ x < r / 2} ×ˢ {y | N₂ y < r / 2} ⊆
          {p : E₁ × E₂ | N₁ p.1 + N₂ p.2 < r} := by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        linarith
      refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsub))
      rw [Measure.prod_prod]
      exact ENNReal.mul_pos (hl₁ _ (half_pos hr)).1 (hl₂ _ (half_pos hr)).1
    · have hsub : {p : E₁ × E₂ | N₁ p.1 + N₂ p.2 < r} ⊆ {x | N₁ x < r} ×ˢ {y | N₂ y < r} := by
        rintro ⟨x, y⟩ hxy
        simp only [Set.mem_setOf_eq, Set.mem_prod] at hxy ⊢
        constructor <;> linarith [hN₁0 x, hN₂0 y]
      refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (hl₁ r hr).2 (hl₂ r hr).2
  rw [tendsto_order]
  constructor
  · intro a ha
    have hc0 : c₁ * c₂ ≠ 0 := (lt_of_le_of_lt bot_le ha).ne'
    have hc₁0 : c₁ ≠ 0 := left_ne_zero_of_mul hc0
    have hc₂0 : c₂ ≠ 0 := right_ne_zero_of_mul hc0
    have hlim : Tendsto (fun t : ℝ≥0∞ => (c₁ - t) * (c₂ - t)) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
      have t1 := (ENNReal.continuous_sub_left hc₁).tendsto 0
      have t2 := (ENNReal.continuous_sub_left hc₂).tendsto 0
      simp only [tsub_zero] at t1 t2
      exact ENNReal.Tendsto.mul (t1.mono_left nhdsWithin_le_nhds) (Or.inr hc₂)
        (t2.mono_left nhdsWithin_le_nhds) (Or.inr hc₁)
    obtain ⟨t, ht, htpos⟩ := ((hlim.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have htpos' : (0 : ℝ≥0∞) < t := htpos
    have ha₁ : c₁ - t < c₁ := ENNReal.sub_lt_self hc₁ hc₁0 htpos'.ne'
    have ha₂ : c₂ - t < c₂ := ENNReal.sub_lt_self hc₂ hc₂0 htpos'.ne'
    obtain ⟨δ₁, hδ₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₁).1 _ ha₁)
    obtain ⟨δ₂, hδ₂, hsub₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₂).1 _ ha₂)
    have hδ : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    obtain ⟨hr0, hrδ⟩ := hr
    have k₁ : ∀ s, 0 < s → s ≤ r → (c₁ - t) * l₁ {x | N₁ x < s} ≤ 1 * m₁ {x | n₁ x < s} := by
      intro s hs hsr
      have hs' : (c₁ - t) < m₁ {x | n₁ x < s} / l₁ {x | N₁ x < s} :=
        hsub₁ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_left _ _))⟩
      rw [one_mul]
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hl₁ s hs).1) (Or.inl (hl₁ s hs).2)).1 hs').le
    have k₂ : ∀ s, 0 < s → s ≤ r → (c₂ - t) * l₂ {x | N₂ x < s} ≤ 1 * m₂ {x | n₂ x < s} := by
      intro s hs hsr
      have hs' : (c₂ - t) < m₂ {x | n₂ x < s} / l₂ {x | N₂ x < s} :=
        hsub₂ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_right _ _))⟩
      rw [one_mul]
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hl₂ s hs).1) (Or.inl (hl₂ s hs).2)).1 hs').le
    have s₁ := mul_prod_sublevel_add_le_of_fst_sublevel_le l₁ m₁ m₂ N₁ n₁ n₂ hN₁ hn₁ hn₂ hN₁0 hn₁0 hn₂0 _ 1 r k₁
    have s₂ := mul_prod_sublevel_add_le_of_snd_sublevel_le l₁ l₂ m₂ N₁ N₂ n₂ hN₁ hN₂ hn₂ hN₁0 hN₂0 hn₂0 _ 1 r k₂
    rw [one_mul] at s₁ s₂
    have key : ((c₁ - t) * (c₂ - t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≤
        (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} :=
      calc ((c₁ - t) * (c₂ - t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}
          = (c₁ - t) * ((c₂ - t) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) := mul_assoc _ _ _
        _ ≤ (c₁ - t) * (l₁.prod m₂) {p | N₁ p.1 + n₂ p.2 < r} := by gcongr
        _ ≤ (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} := s₁
    exact lt_of_lt_of_le ht
      ((ENNReal.le_div_iff_mul_le (Or.inl (hG r hr0).1) (Or.inl (hG r hr0).2)).2 key)
  · intro b hb
    have hlim : Tendsto (fun t : ℝ≥0∞ => (c₁ + t) * (c₂ + t)) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
      have t1 : Tendsto (fun t : ℝ≥0∞ => c₁ + t) (𝓝 0) (𝓝 (c₁ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      have t2 : Tendsto (fun t : ℝ≥0∞ => c₂ + t) (𝓝 0) (𝓝 (c₂ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at t1 t2
      exact ENNReal.Tendsto.mul (t1.mono_left nhdsWithin_le_nhds) (Or.inr hc₂)
        (t2.mono_left nhdsWithin_le_nhds) (Or.inr hc₁)
    obtain ⟨t, ht, htpos⟩ := ((hlim.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have htpos' : (0 : ℝ≥0∞) < t := htpos
    have hb₁ : c₁ < c₁ + t := ENNReal.lt_add_right hc₁ htpos'.ne'
    have hb₂ : c₂ < c₂ + t := ENNReal.lt_add_right hc₂ htpos'.ne'
    obtain ⟨δ₁, hδ₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₁).2 _ hb₁)
    obtain ⟨δ₂, hδ₂, hsub₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₂).2 _ hb₂)
    have hδ : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    obtain ⟨hr0, hrδ⟩ := hr
    have k₁ : ∀ s, 0 < s → s ≤ r → 1 * m₁ {x | n₁ x < s} ≤ (c₁ + t) * l₁ {x | N₁ x < s} := by
      intro s hs hsr
      have hs' : m₁ {x | n₁ x < s} / l₁ {x | N₁ x < s} < c₁ + t :=
        hsub₁ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_left _ _))⟩
      rw [one_mul]
      exact ((ENNReal.div_lt_iff (Or.inl (hl₁ s hs).1) (Or.inl (hl₁ s hs).2)).1 hs').le
    have k₂ : ∀ s, 0 < s → s ≤ r → 1 * m₂ {x | n₂ x < s} ≤ (c₂ + t) * l₂ {x | N₂ x < s} := by
      intro s hs hsr
      have hs' : m₂ {x | n₂ x < s} / l₂ {x | N₂ x < s} < c₂ + t :=
        hsub₂ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_right _ _))⟩
      rw [one_mul]
      exact ((ENNReal.div_lt_iff (Or.inl (hl₂ s hs).1) (Or.inl (hl₂ s hs).2)).1 hs').le
    have s₁ := mul_prod_sublevel_add_le_of_fst_sublevel_le m₁ l₁ m₂ n₁ N₁ n₂ hn₁ hN₁ hn₂ hn₁0 hN₁0 hn₂0 1 _ r k₁
    have s₂ := mul_prod_sublevel_add_le_of_snd_sublevel_le l₁ m₂ l₂ N₁ n₂ N₂ hN₁ hn₂ hN₂ hN₁0 hn₂0 hN₂0 1 _ r k₂
    rw [one_mul] at s₁ s₂
    have key : (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} ≤
        ((c₁ + t) * (c₂ + t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} :=
      calc (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r}
          ≤ (c₁ + t) * (l₁.prod m₂) {p | N₁ p.1 + n₂ p.2 < r} := s₁
        _ ≤ (c₁ + t) * ((c₂ + t) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) :=
          by gcongr
        _ = ((c₁ + t) * (c₂ + t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} :=
          (mul_assoc _ _ _).symm
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul key) ht

end GlobalTheory.SublevelDensity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionProductEqSqrtTwo
section
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.WeberProduct

def eulerProd (x : ℂ) : ℂ := ∏' n : ℕ, (1 - x ^ (n + 1))

def oddProd (x : ℂ) : ℂ := ∏' k : ℕ, (1 - x ^ (2 * k + 1))

theorem multipliable_odd {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun k : ℕ ↦ 1 - x ^ (2 * k + 1) := by
  have h2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hs : Summable fun k : ℕ ↦ ‖x‖ * (‖x‖ ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) h2).mul_left _
  have := multipliable_one_add_of_summable (f := fun k : ℕ ↦ -x ^ (2 * k + 1))
    (hs.congr fun k ↦ by simp [norm_pow, pow_succ, pow_mul]; ring)
  simpa [sub_eq_add_neg] using this

theorem multipliable_euler {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - x ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow hx

theorem eulerProd_split {y : ℂ} (hy : ‖y‖ < 1) : eulerProd y = oddProd y * eulerProd (y ^ 2) := by
  have hy2 : ‖y ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg y]
  have e1 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k)) = fun k ↦ 1 - y ^ (2 * k + 1) := rfl
  have e2 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k + 1)) =
      fun k ↦ 1 - (y ^ 2) ^ (k + 1) := by
    funext k; rw [← pow_mul]; ring_nf
  have h := tprod_even_mul_odd (f := fun n : ℕ ↦ 1 - y ^ (n + 1))
    (by rw [e1]; exact multipliable_odd hy) (by rw [e2]; exact multipliable_euler hy2)
  rw [e1, e2] at h
  rw [eulerProd, eulerProd, oddProd, h]

theorem oddProd_neg_mul {t : ℂ} (ht : ‖t‖ < 1) : oddProd (-t) * oddProd t = oddProd (t ^ 2) := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  rw [oddProd, oddProd, oddProd, ← (multipliable_odd hn).tprod_mul (multipliable_odd ht)]
  congr 1
  funext k
  rw [Odd.neg_pow ⟨k, rfl⟩, ← pow_mul]
  ring_nf

theorem eulerProd_identity {t : ℂ} (ht : ‖t‖ < 1) :
    eulerProd (-t) * eulerProd t * eulerProd (t ^ 4) = eulerProd (t ^ 2) ^ 3 := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  have h2 : ‖t ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg t]
  have a := eulerProd_split hn
  have b := eulerProd_split ht
  have c := eulerProd_split h2
  rw [neg_sq] at a
  rw [← pow_mul] at c
  norm_num at c
  have d := oddProd_neg_mul ht
  norm_num at c
  linear_combination (eulerProd t * eulerProd (t ^ 4)) * a + (oddProd (-t) * eulerProd (t ^ 2) * eulerProd (t ^ 4)) * b +
    (eulerProd (t ^ 2) ^ 2 * eulerProd (t ^ 4)) * d - eulerProd (t ^ 2) ^ 2 * c

theorem eta_eq (z : ℂ) : ModularForm.eta z = Function.Periodic.qParam 24 z * eulerProd (Function.Periodic.qParam 1 z) :=
  rfl

theorem eta_relation (τ : ℍ) :
    cexp (-(π * I / 24)) * ModularForm.eta (((τ : ℂ) + 1) / 2) * ModularForm.eta ((τ : ℂ) / 2) *
      ModularForm.eta (2 * (τ : ℂ)) = ModularForm.eta τ ^ 3 := by
  set t := cexp (π * I * (τ : ℂ)) with ht_def
  have ht : ‖t‖ < 1 := by
    rw [ht_def, Complex.norm_exp, Real.exp_lt_one_iff]
    have := τ.im_pos
    simp only [mul_re, ofReal_re, Complex.I_re, ofReal_im, Complex.I_im, mul_im, coe_re, coe_im]
    nlinarith [Real.pi_pos]
  have q1 : Function.Periodic.qParam 1 (((τ : ℂ) + 1) / 2) = -t := by
    rw [Function.Periodic.qParam, ht_def, ← mul_neg_one, ← Complex.exp_pi_mul_I, ← Complex.exp_add]
    congr 1; push_cast; ring
  have q2 : Function.Periodic.qParam 1 ((τ : ℂ) / 2) = t := by
    rw [Function.Periodic.qParam, ht_def]; congr 1; push_cast; ring
  have q3 : Function.Periodic.qParam 1 (2 * (τ : ℂ)) = t ^ 4 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have q4 : Function.Periodic.qParam 1 (τ : ℂ) = t ^ 2 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hq : cexp (-(π * I / 24)) * Function.Periodic.qParam 24 (((τ : ℂ) + 1) / 2) *
      Function.Periodic.qParam 24 ((τ : ℂ) / 2) * Function.Periodic.qParam 24 (2 * (τ : ℂ)) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 3 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [eta_eq, eta_eq, eta_eq, eta_eq, q1, q2, q3, q4]
  have key := eulerProd_identity ht
  linear_combination (eulerProd (-t) * eulerProd t * eulerProd (t ^ 4)) * hq +
    Function.Periodic.qParam 24 (τ : ℂ) ^ 3 * key

theorem weber_prod (τ : ℍ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ =
      ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h0 : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.2
  have key := eta_relation τ
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂]
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_iff (by simp [h0])]
  linear_combination ((Real.sqrt 2 : ℝ) : ℂ) * key

end GlobalTheory.WeberProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionsRootsOfCubicOfHalfPeriodDiff
section
open Complex

open Polynomial
open UpperHalfPlane hiding I

noncomputable section

namespace GlobalTheory.WeberCubicAlgebra

lemma half_root (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
  have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, h2⟩
  rw [L.derivWeierstrassP_neg] at e1
  have e2 : -t + 2 * t = t := by ring
  simp only [e2] at e1
  have e3 : L.derivWeierstrassP t = 0 := by linear_combination e1 / 2
  rw [← L.derivWeierstrassP_sq t ht, e3]
  simp

lemma roots_alg {e1 e2 e3 g h P A B D : ℂ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (r1 : 4 * e1 ^ 3 - g * e1 - h = 0) (r2 : 4 * e2 ^ 3 - g * e2 - h = 0)
    (r3 : 4 * e3 ^ 3 - g * e3 - h = 0)
    (d1 : e1 - e2 = P * A) (d2 : e1 - e3 = P * B) (d3 : e3 - e2 = P * D) :
    g = 2 / 3 * P ^ 2 * (A ^ 2 + B ^ 2 + D ^ 2) ∧
      g ^ 3 - 27 * h ^ 2 = 16 * P ^ 6 * (A * B * D) ^ 2 := by
  have a12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination r1 - r2)
  have a13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination r1 - r3)
  have s : e1 + e2 + e3 = 0 := by
    have : (e2 - e3) * (e1 + e2 + e3) = (e2 - e3) * 0 := by linear_combination (a12 - a13) / 4
    exact mul_left_cancel₀ (sub_ne_zero.2 h23) this
  have hh : h = 4 * e1 ^ 3 - g * e1 := by linear_combination -r1
  have k1 : (P * A) ^ 2 = (e1 - e2) ^ 2 := by rw [d1]
  have k2 : (P * B) ^ 2 = (e1 - e3) ^ 2 := by rw [d2]
  have k3 : (P * D) ^ 2 = (e3 - e2) ^ 2 := by rw [d3]
  obtain rfl : e3 = -e1 - e2 := by linear_combination s
  subst hh
  subst a12
  constructor
  · linear_combination (-2 / 3 : ℂ) * (k1 + k2 + k3)
  · have : 16 * P ^ 6 * (A * B * D) ^ 2 = 16 * ((P * A) ^ 2 * (P * B) ^ 2 * (P * D) ^ 2) := by ring
    rw [this, k1, k2, k3]
    ring

lemma coeffs (A B D j F0 F1 F2 : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (hs : A = B + D)
    (h0 : F0 * (B * D) = 16 * A ^ 2) (h1 : F1 * (A * D) = 16 * B ^ 2)
    (h2 : F2 * (A * B) = 16 * D ^ 2) (hj : j * (A * B * D) ^ 2 = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3) :
    F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096 := by
  have e0 : F0 = 16 * A ^ 2 / (B * D) := by rw [eq_div_iff (mul_ne_zero hB hD)]; exact h0
  have e1 : F1 = 16 * B ^ 2 / (A * D) := by rw [eq_div_iff (mul_ne_zero hA hD)]; exact h1
  have e2 : F2 = 16 * D ^ 2 / (A * B) := by rw [eq_div_iff (mul_ne_zero hA hB)]; exact h2
  have ej : j = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3 / (A * B * D) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hA hB) hD))]; exact hj
  subst e0 e1 e2 ej hs
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

lemma cubic_eq (j F0 F1 F2 : ℂ)
    (h : F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096) :
    ((X - C 16) ^ 3 - C j * X : ℂ[X]) = (X - C F0) * (X - C (-F1)) * (X - C (-F2)) := by
  obtain ⟨s1, s2, s3⟩ := h
  have e : ((X - C F0) * (X - C (-F1)) * (X - C (-F2)) : ℂ[X]) =
      X ^ 3 - C (F0 - F1 - F2) * X ^ 2 + C (-(F0 * F1) - F0 * F2 + F1 * F2) * X - C (F0 * F1 * F2) := by
    simp only [map_sub, map_neg, map_mul, map_add (f := _)]
    ring
  rw [e, s1, s2, s3]
  simp only [map_sub, map_ofNat]
  ring

end GlobalTheory.WeberCubicAlgebra

namespace GlobalTheory.WeberCubicAlgebra


open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber in
theorem weberCubic_of_halfPeriodDiff : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.WeberCubic τ := by
  intro τ hd hj hw
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨w0, w1, w2⟩ := hw
  unfold JacobiProduct at hj
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : thetaConst 0 0 τ * thetaConst 0 1 τ * thetaConst 1 0 τ ≠ 0 := by
    rw [hj]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have t0 : thetaConst 0 0 τ ≠ 0 := fun h => hprod (by simp [h])
  have t1 : thetaConst 0 1 τ ≠ 0 := fun h => hprod (by simp [h])
  have t2 : thetaConst 1 0 τ ≠ 0 := fun h => hprod (by simp [h])
  obtain ⟨n1, n2, n3⟩ := halfPeriods_notMem τ
  have mem : ∀ p q : ℤ, ((p : ℂ) * (τ : ℂ) + q) ∈ (GlobalTheory.periodPairOfTau τ).lattice := fun p q => by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨p, q, by ring⟩
  have r1 := half_root (GlobalTheory.periodPairOfTau τ) (t := 1 / 2) (by simpa using mem 0 1) n1
  have r2 := half_root (GlobalTheory.periodPairOfTau τ) (t := (τ : ℂ) / 2) (by
    have := mem 1 0
    convert this using 1
    push_cast
    ring) n2
  have r3 := half_root (GlobalTheory.periodPairOfTau τ) (t := (1 + (τ : ℂ)) / 2) (by
    have := mem 1 1
    convert this using 1
    push_cast
    ring) n3
  have hP : ((Real.pi : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ hp
  have h12 : wp τ (1 / 2) ≠ wp τ ((τ : ℂ) / 2) := by
    rw [← sub_ne_zero, d1]
    exact mul_ne_zero hP (pow_ne_zero _ t0)
  have h13 : wp τ (1 / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    rw [← sub_ne_zero, d2]
    exact mul_ne_zero hP (pow_ne_zero _ t1)
  have h23 : wp τ ((τ : ℂ) / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    intro h
    have h' : wp τ ((1 + (τ : ℂ)) / 2) - wp τ ((τ : ℂ) / 2) = 0 := by rw [h]; ring
    rw [d3] at h'
    exact mul_ne_zero hP (pow_ne_zero _ t2) h'
  have hw1 : wp τ (1 / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP (1 / 2) := rfl
  have hw2 : wp τ ((τ : ℂ) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((τ : ℂ) / 2) := rfl
  have hw3 : wp τ ((1 + (τ : ℂ)) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((1 + (τ : ℂ)) / 2) := rfl
  rw [← hw1] at r1
  rw [← hw2] at r2
  rw [← hw3] at r3
  obtain ⟨hg, hdisc⟩ := roots_alg h12 h13 h23 r1 r2 r3 d1 d2 d3
  have hjl : jLat τ * ((GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ).g₃ ^ 2) =
      1728 * (GlobalTheory.periodPairOfTau τ).g₂ ^ 3 := by
    rw [jLat_eq, div_mul_cancel₀ _ (disc_ne_zero τ)]
  rw [hdisc, hg] at hjl
  have hs : thetaConst 0 0 τ ^ 4 = thetaConst 0 1 τ ^ 4 + thetaConst 1 0 τ ^ 4 := by
    apply mul_left_cancel₀ hP
    linear_combination -d1 + d2 + d3
  have hJ4 : thetaConst 0 0 τ ^ 4 * thetaConst 0 1 τ ^ 4 * thetaConst 1 0 τ ^ 4 =
      16 * ModularForm.eta (τ : ℂ) ^ 12 := by
    have := congrArg (· ^ 4) hj
    linear_combination this
  have a0 : (thetaConst 0 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF τ ^ 24 := by
    rw [w0]; ring
  have a1 : (thetaConst 0 1 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₁ τ ^ 24 := by
    rw [w1]; ring
  have a2 : (thetaConst 1 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₂ τ ^ 24 := by
    rw [w2]; ring
  have A0 := pow_ne_zero 4 t0
  have B0 := pow_ne_zero 4 t1
  have D0 := pow_ne_zero 4 t2
  apply cubic_eq
  apply coeffs _ _ _ _ _ _ _ A0 B0 D0 hs
  · apply mul_left_cancel₀ A0
    linear_combination weberF τ ^ 24 * hJ4 - 16 * a0
  · apply mul_left_cancel₀ B0
    linear_combination weberF₁ τ ^ 24 * hJ4 - 16 * a1
  · apply mul_left_cancel₀ D0
    linear_combination weberF₂ τ ^ 24 * hJ4 - 16 * a2
  · have h16 : (16 : ℂ) * ((Real.pi : ℂ) ^ 2) ^ 6 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hP)
    apply mul_left_cancel₀ h16
    linear_combination hjl

end GlobalTheory.WeberCubicAlgebra
end
end

