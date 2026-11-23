module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
section
noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

private theorem exists_bump {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] (H : Set G)
    (hH : IsClosed H) (h1 : (1 : G) ∈ H) (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) :
    ∃ f : G → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, ∃ h ∈ H, 0 < f (h * x)) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ ∀ g ∈ H * C, f g ≠ 0 → g ∈ D := by
  classical
  let L : CompactExhaustion G := (CompactExhaustion.choice G).shiftr
  have L0 : L 0 = ∅ := rfl
  let A : ℕ → Set G := fun n => H * L n
  let O : ℕ → Set G := fun n => H * interior (L n)
  have hA : ∀ n, IsClosed (A n) := fun n => hH.mul_right_of_isCompact (L.isCompact n)
  have hO : ∀ n, IsOpen (O n) := fun n => isOpen_interior.mul_left
  have hOA : ∀ n, O n ⊆ A n := fun n => mul_subset_mul_left interior_subset
  have hAO : ∀ n, A n ⊆ O (n + 1) := fun n => mul_subset_mul_left (L.subset_interior_succ n)
  have hAm : Monotone A := fun a b h => mul_subset_mul_left (L.subset h)
  have hA0 : A 0 = ∅ := by simp [A, L0]
  have hLA : ∀ n, (L n : Set G) ⊆ A n := fun n x hx => ⟨1, h1, x, hx, one_mul x⟩
  have hdisj : ∀ n, Disjoint ((L (n + 1) : Set G) \ O n) (A (n - 1)) := by
    intro n
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ hxA
    cases n with
    | zero => simp [hA0] at hxA
    | succ n => exact hx (hAO n hxA)
  have hex : ∀ n, ∃ φ : C(G, ℝ), EqOn φ 1 ((L (n + 1) : Set G) \ O n) ∧ EqOn φ 0 (A (n - 1)) ∧
      HasCompactSupport φ ∧ ∀ x, φ x ∈ Icc (0 : ℝ) 1 := fun n =>
    exists_continuous_one_zero_of_isCompact ((L.isCompact (n + 1)).diff (hO n)) (hA (n - 1))
      (hdisj n)
  choose φ hφ1 hφ0 hφc hφI using hex
  have hvan : ∀ n k x, k < n → x ∈ A k → φ n x = 0 := fun n k x hkn hx =>
    hφ0 n (hAm (Nat.le_sub_one_of_lt hkn) hx)
  have hlf : LocallyFinite fun n => Function.support (φ n) := by
    intro x
    obtain ⟨k, hk⟩ := L.exists_mem_nhds x
    refine ⟨_, hk, (Set.finite_Iic k).subset ?_⟩
    rintro n ⟨y, hy, hyk⟩
    by_contra hn
    exact hy (hvan n k y (not_le.mp hn) (hLA k hyk))
  refine ⟨fun x => ∑ᶠ n, φ n x, continuous_finsum (fun n => (φ n).continuous) hlf,
    fun x => finsum_nonneg fun n => (hφI n x).1, ?_, ?_⟩
  · intro x
    have hexA : ∃ m, x ∈ A m := by
      obtain ⟨k, hk⟩ := L.exists_mem_nhds x
      exact ⟨k, hLA k (mem_of_mem_nhds hk)⟩
    have hm0 : Nat.find hexA ≠ 0 := by
      intro h0
      have := Nat.find_spec hexA
      rw [h0, hA0] at this
      exact this
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hxn : x ∉ A n := Nat.find_min hexA (by omega)
    have hxs : x ∈ A (n + 1) := by
      have := Nat.find_spec hexA
      rwa [hn] at this
    obtain ⟨h, hh, y, hy, rfl⟩ := hxs
    have hyO : y ∉ O n := by
      intro hyO
      obtain ⟨h', hh', z, hz, rfl⟩ := hyO
      exact hxn (hOA n ⟨h * h', hmul _ hh _ hh', z, hz, by simp [mul_assoc]⟩)
    refine ⟨h⁻¹, hinv h hh, ?_⟩
    have hy1 : φ n y = 1 := hφ1 n ⟨hy, hyO⟩
    have hfin : (Function.support fun m => φ m y).Finite := hlf.point_finite y
    have hle := single_le_finsum (f := fun m => φ m y) n hfin (fun m => (hφI m y).1)
    simp only [inv_mul_cancel_left]
    have : (1 : ℝ) ≤ ∑ᶠ m, φ m y := by simpa [hy1] using hle
    linarith
  · intro C hC
    obtain ⟨k, hk⟩ := L.exists_superset_of_isCompact hC
    refine ⟨⋃ n ∈ Finset.range (k + 1), tsupport (φ n),
      (Finset.range (k + 1)).isCompact_biUnion fun n _ => hφc n, ?_⟩
    intro g hg hfg
    have hgA : g ∈ A k := mul_subset_mul_left hk hg
    obtain ⟨n, hn⟩ : ∃ n, φ n g ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hfg (by simp [hcon])
    have hnk : n ≤ k := by
      by_contra hnk
      exact hn (hvan n k g (not_le.mp hnk) hgA)
    exact mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
      (subset_tsupport _ hn)

private theorem exists_nrm {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [MeasurableSpace T] [BorelSpace T]
    (j : T →* G) (hj : IsClosedEmbedding j) (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] (f : G → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hpos : ∀ x, ∃ h ∈ Set.range j, 0 < f (h * x))
    (hsupp : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ g ∈ Set.range j * C, f g ≠ 0 → g ∈ D) :
    ∃ ρ : G → NNReal, Continuous ρ ∧ IsNrm j ν (fun g => ρ g) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
        ∀ g ∈ Set.range j * C, ρ g ≠ 0 → g ∈ D := by
  have hcont2 : Continuous fun p : G × T => f (j p.2 * p.1) :=
    hf.comp ((hj.continuous.comp continuous_snd).mul continuous_fst)
  have hk : ∀ N : Set G, IsCompact N → ∃ k : Set T, IsCompact k ∧
      ∀ x ∈ N, ∀ t, t ∉ k → f (j t * x) = 0 := by
    intro N hN
    obtain ⟨D, hD, hDs⟩ := hsupp N hN
    refine ⟨j ⁻¹' (D * N⁻¹), hj.isCompact_preimage (hD.mul hN.inv), ?_⟩
    intro x hx t ht
    by_contra hne
    apply ht
    have hmem := hDs (j t * x) ⟨j t, mem_range_self t, x, hx, rfl⟩ hne
    exact ⟨j t * x, hmem, x⁻¹, Set.inv_mem_inv.mpr hx, by simp⟩
  have hcs : ∀ x, HasCompactSupport fun t => f (j t * x) := by
    intro x
    obtain ⟨k, hkc, hks⟩ := hk {x} isCompact_singleton
    exact HasCompactSupport.intro hkc fun t ht => hks x rfl t ht
  have hc1 : ∀ x, Continuous fun t => f (j t * x) := fun x =>
    hcont2.comp (Continuous.prodMk continuous_const continuous_id)
  have hint : ∀ x, Integrable (fun t => f (j t * x)) ν := fun x =>
    (hc1 x).integrable_of_hasCompactSupport (hcs x)
  let I : G → ℝ := fun x => ∫ t, f (j t * x) ∂ν
  have hIc : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨N, hNc, hNx⟩ := exists_compact_mem_nhds x
    obtain ⟨k, hkc, hks⟩ := hk N hNc
    have : ContinuousOn I N :=
      continuousOn_integral_of_compact_support (f := fun x t => f (j t * x)) hkc
        hcont2.continuousOn fun p t hp ht => hks p hp t ht
    exact this.continuousAt hNx
  have hIpos : ∀ x, 0 < I x := by
    intro x
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hpos x
    exact (hc1 x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun s => hf0 _) ht.ne'
  have hIinv : ∀ s x, I (j s * x) = I x := by
    intro s x
    have := integral_mul_right_eq_self (μ := ν) (fun t => f (j t * x)) s
    simpa [I, mul_assoc] using this
  refine ⟨fun g => Real.toNNReal (f g / I g),
    continuous_real_toNNReal.comp (hf.div hIc fun x => (hIpos x).ne'), ⟨?_, ?_⟩, ?_⟩
  · exact measurable_coe_nnreal_ennreal.comp
      (continuous_real_toNNReal.comp (hf.div hIc fun x => (hIpos x).ne')).measurable
  · intro x
    have hrw : ∀ t, ((Real.toNNReal (f (j t * x) / I (j t * x)) : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal (f (j t * x) / I x) := fun t => by rw [hIinv]; rfl
    simp_rw [hrw]
    rw [← ofReal_integral_eq_lintegral_ofReal ((hint x).div_const _)
      (Filter.Eventually.of_forall fun t => div_nonneg (hf0 _) (hIpos x).le), integral_div]
    rw [div_self (hIpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨D, hD, hDs⟩ := hsupp C hC
    refine ⟨D, hD, fun g hg hne => hDs g hg ?_⟩
    intro h0
    apply hne
    simp [h0]

theorem normEx : NormEx := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hp
  obtain ⟨-, hj, hν⟩ := hp
  haveI := hν.1
  haveI := hν.2
  haveI : ν.IsMulRightInvariant := by
    have h : ν.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  obtain ⟨f, hf, hf0, hpos, hsupp⟩ := exists_bump (Set.range j) hj.isClosed_range
    ⟨1, map_one j⟩ (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul j a b⟩)
    (by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv j a⟩)
  exact exists_nrm j hj ν f hf hf0 hpos hsupp

end UpperTheory.ConvolutionTheory.G
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
section
open MeasureTheory Topology
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {T : Type} [Group T] [TopologicalSpace T]
    [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] {μ : Measure G} {j : T →* G} {ν : Measure T}

private theorem lint_eq (hp : Pair μ j ν) {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) (hi : ∀ t g, Φ (j t * g) = Φ g)
    {ρ ρ' : G → ℝ≥0∞} (h : IsNrm j ν ρ) (h' : IsNrm j ν ρ') :
    ∫⁻ x, Φ x * ρ x ∂μ = ∫⁻ x, Φ x * ρ' x ∂μ := by
  obtain ⟨⟨hμ, -⟩, hj, hν, hν'⟩ := hp
  have hjm : Measurable j := hj.continuous.measurable
  have hm := h.1
  have hm' := h'.1
  calc ∫⁻ x, Φ x * ρ x ∂μ = ∫⁻ x, ∫⁻ t, Φ x * ρ x * ρ' (j t * x) ∂ν ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ (by fun_prop), h'.2, mul_one]
    _ = ∫⁻ t, ∫⁻ x, Φ x * ρ x * ρ' (j t * x) ∂μ ∂ν :=
        lintegral_lintegral_swap (Measurable.aemeasurable (by unfold Function.uncurry; fun_prop))
    _ = ∫⁻ t, ∫⁻ x, Φ x * ρ' x * ρ (j t⁻¹ * x) ∂μ ∂ν := by
        refine lintegral_congr fun t => ?_
        rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * ρ x * ρ' (j t * x)) (j t⁻¹)]
        refine lintegral_congr fun x => ?_
        rw [hi, ← mul_assoc (j t), ← map_mul, mul_inv_cancel, map_one, one_mul, mul_right_comm]
    _ = ∫⁻ x, ∫⁻ t, Φ x * ρ' x * ρ (j t⁻¹ * x) ∂ν ∂μ :=
        (lintegral_lintegral_swap (Measurable.aemeasurable (by unfold Function.uncurry; fun_prop))).symm
    _ = ∫⁻ x, Φ x * ρ' x ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_eq_self (μ := ν) (fun t => ρ (j t * x)), h.2,
          mul_one]

private theorem ae_lt_top_nrm (hp : Pair μ j ν) {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) : ∀ᵐ x ∂μ, ρ x < ⊤ := by
  obtain ⟨⟨hμ, -⟩, hj, hν, hν'⟩ := hp
  have hjm : Measurable j := hj.continuous.measurable
  have hm := h.1
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ t ∂ν, ρ (j t * x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ae_lt_top (by fun_prop) (by rw [h.2]; exact ENNReal.one_ne_top)
  have hs : MeasurableSet {p : G × T | ρ (j p.2 * p.1) < ⊤} :=
    measurableSet_lt (by fun_prop) measurable_const
  have h2 : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ρ (j t * x) < ⊤ := (Measure.ae_ae_comm hs).1 h1
  obtain ⟨t, ht⟩ := h2.exists
  have := (measurePreserving_mul_left μ (j t)⁻¹).quasiMeasurePreserving.ae ht
  simpa using this

private theorem map_eq (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F) (hi : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (h : IsNrm j ν ρ) (h' : IsNrm j ν ρ') :
    (μ.withDensity ρ).map F = (μ.withDensity ρ').map F := by
  ext s hs
  have key := lint_eq hp (Φ := fun x => s.indicator 1 (F x)) ((measurable_one.indicator hs).comp hF)
    (fun t g => by rw [hi]) h h'
  have e : ∀ r : G → ℝ≥0∞, (μ.withDensity r).map F s = ∫⁻ x, s.indicator 1 (F x) * r x ∂μ := fun r => by
    rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), ← lintegral_indicator (hF hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : F x ∈ s <;> simp [Set.indicator, hx]
  rw [e, e, key]

private theorem int_eq (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F)
    {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) :
    ∫ x, F x * ((ρ x).toReal : ℂ) ∂μ = ∫ z, z ∂((μ.withDensity ρ).map F) := by
  rw [integral_map hF.aemeasurable (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul h.1 (ae_lt_top_nrm hp h)]
  simp only [Complex.real_smul, mul_comm]

private theorem integrable_iff (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F)
    {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) :
    Integrable (fun x => F x * ((ρ x).toReal : ℂ)) μ ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤ := by
  have hm := h.1
  have e : ∫⁻ x, ‖F x * ((ρ x).toReal : ℂ)‖ₑ ∂μ = ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_nrm hp h] with x hx
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((ρ x).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [← e, ← lt_top_iff_ne_top]
  exact ⟨fun h => h.2, fun h => ⟨Measurable.aestronglyMeasurable (by fun_prop), h⟩⟩

end

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.quotEq :
    UpperTheory.ConvolutionTheory.G.QuotEq := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hp F hF hi ρ h
  have h2 : QInt μ j ν F ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤ := by
    refine ⟨fun hq => (integrable_iff hp hF h).1 (hq.2.2 ρ h), fun hq => ⟨hF, hi, fun ρ' h' => ?_⟩⟩
    rw [integrable_iff hp hF h', lint_eq hp (Φ := fun x => ‖F x‖ₑ) hF.enorm (fun t g => by rw [hi]) h' h]
    exact hq
  refine ⟨h2.trans (integrable_iff hp hF h).symm, h2, ?_⟩
  have hex : ∃ ρ, IsNrm j ν ρ := ⟨ρ, h⟩
  rw [qI, dite_eq_left hex, int_eq hp hF hex.choose_spec, int_eq hp hF h, map_eq hp hF hi hex.choose_spec h]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotFub
section
open MeasureTheory in
theorem UpperTheory.ConvolutionTheory.G.quotFub_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotFub := by
  intro _ hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP X _ m _ F hF hinv ρ hρ hfin
  haveI : μ.IsHaarMeasure := hP.1.1
  have hρm : Measurable (fun x => ((ρ x).toReal : ℂ)) :=
    Complex.measurable_ofReal.comp hρ.1.ennreal_toReal
  have hH : Measurable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) :=
    hF.mul (hρm.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) (m.prod μ) := by
    refine ⟨hH.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ hH.enorm.aemeasurable]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfin)
    refine lintegral_mono fun a => lintegral_mono fun x => ?_
    simp only [Function.uncurry, enorm_mul]
    gcongr
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hGm : Measurable (fun g => ∫ a, F a g ∂m) :=
    (hF.stronglyMeasurable.integral_prod_left).measurable
  have hGi : ∀ t g, (fun g => ∫ a, F a g ∂m) (j t * g) = (fun g => ∫ a, F a g ∂m) g := by
    intro t g
    simp only [hinv]
  obtain ⟨h1, -, h3⟩ := hE G T μ j ν hP _ hGm hGi ρ hρ
  have hmul : ∀ x, (∫ a, F a x ∂m) * ((ρ x).toReal : ℂ) = ∫ a, F a x * ((ρ x).toReal : ℂ) ∂m :=
    fun x => (integral_mul_const _ _).symm
  refine ⟨h1.2 ?_, ?_⟩
  · simp only [hmul]
    exact hint.integral_prod_right
  · rw [h3]
    simp only [hmul]
    rw [← integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact ((hE G T μ j ν hP (F a) (hF.of_uncurry_left) (hinv a) ρ hρ).2.2).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotLin
section
open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section

variable {G T : Type} [Group G] [MeasurableSpace G] [Group T] [MeasurableSpace T]

private theorem smul_coe (a : NNReal) (μ : Measure G) : a • μ = (a : ℝ≥0∞) • μ := rfl

private theorem uni_smul [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G}
    (h : Uni μ) {a : NNReal} (ha : a ≠ 0) : Uni (a • μ) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨Measure.IsHaarMeasure.nnreal_smul μ ha,
    ⟨by
      rw [Measure.inv, Measure.map_smul, Measure.map_inv_eq_self]
      exact continuous_inv.measurable.aemeasurable⟩⟩

private theorem isNrm_div {j : T →* G} {ν : Measure T} {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ)
    {b : NNReal} (hb : b ≠ 0) : IsNrm j (b • ν) (fun x => (b : ℝ≥0∞)⁻¹ * ρ x) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by simpa using hb
  refine ⟨h.1.const_mul _, fun x => ?_⟩
  rw [smul_coe, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hb0), h.2 x,
    mul_one, smul_eq_mul, ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top]

private theorem isNrm_mul {j : T →* G} {ν : Measure T} {ρ : G → ℝ≥0∞} {b : NNReal}
    (h : IsNrm j (b • ν) ρ) : IsNrm j ν (fun x => (b : ℝ≥0∞) * ρ x) := by
  refine ⟨h.1.const_mul _, fun x => ?_⟩
  have := h.2 x
  rw [smul_coe, lintegral_smul_measure, smul_eq_mul] at this
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, this]

private theorem mul_toReal (z : ℂ) (b : NNReal) (r : ℝ≥0∞) :
    z * ((((b : ℝ≥0∞)⁻¹ * r).toReal : ℝ) : ℂ) = (((b : ℝ) : ℂ))⁻¹ * (z * ((r.toReal : ℝ) : ℂ)) := by
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]
  push_cast
  ring

private theorem int_iff {μ : Measure G} {F : G → ℂ} {ρ : G → ℝ≥0∞} {a b : NNReal} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Integrable (fun x => F x * ((((b : ℝ≥0∞)⁻¹ * ρ x).toReal : ℝ) : ℂ)) (a • μ) ↔
      Integrable (fun x => F x * (((ρ x).toReal : ℝ) : ℂ)) μ := by
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by simpa using ha
  have hc : ((b : ℝ) : ℂ) ≠ 0 := by simpa using hb
  rw [smul_coe, integrable_smul_measure ha0 ENNReal.coe_ne_top]
  simp only [mul_toReal]
  constructor
  · intro h
    have := h.const_mul (((b : ℝ) : ℂ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    exact mul_inv_cancel_left₀ hc _
  · exact fun h => h.const_mul _

private theorem qInt_iff {μ : Measure G} {j : T →* G} {ν : Measure T} {F : G → ℂ} {a b : NNReal}
    (ha : a ≠ 0) (hb : b ≠ 0) : QInt (a • μ) j (b • ν) F ↔ QInt μ j ν F := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by simpa using hb
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun ρ hρ => (int_iff ha hb).1 (h3 _ (isNrm_div hρ hb))⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun ρ hρ => ?_⟩
    have := (int_iff (μ := μ) (ρ := fun x => (b : ℝ≥0∞) * ρ x) (F := F) ha hb).2 (h3 _ (isNrm_mul hρ))
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hb0 ENNReal.coe_ne_top, one_mul] using this

end

end UpperTheory.ConvolutionTheory.G

open UpperTheory.ConvolutionTheory.G in
theorem UpperTheory.ConvolutionTheory.G.quotLin_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotLin := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP
  obtain ⟨ρ₀, -, hρ₀, -⟩ := hN G T μ j ν hP
  refine ⟨fun ι s c F hF => ?_, fun a b ha hb => ?_⟩
  · have hsum : QInt μ j ν (fun g => ∑ i ∈ s, c i * F i g) := by
      refine ⟨Finset.measurable_sum s fun i hi => measurable_const.mul (hF i hi).1,
        fun t g => Finset.sum_congr rfl fun i hi => by rw [(hF i hi).2.1], fun ρ hρ => ?_⟩
      have := integrable_finsetSum s (fun i hi => ((hF i hi).2.2 ρ hρ).const_mul (c i))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Finset.sum_mul, mul_assoc]
    refine ⟨hsum, ?_⟩
    rw [(hE G T μ j ν hP _ hsum.1 hsum.2.1 _ hρ₀).2.2,
      Finset.sum_congr rfl fun i hi => by
        rw [(hE G T μ j ν hP _ (hF i hi).1 (hF i hi).2.1 _ hρ₀).2.2]]
    simp only [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum s fun i hi => ((hF i hi).2.2 _ hρ₀).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · have hP' : Pair (a • μ) j (b • ν) := ⟨uni_smul hP.1 ha, hP.2.1, uni_smul hP.2.2 hb⟩
    refine ⟨hP', fun F hF hinv => ⟨qInt_iff ha hb, ?_⟩⟩
    have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using hb
    rw [(hE G T _ _ _ hP' F hF hinv _ (isNrm_div hρ₀ hb)).2.2, (hE G T μ j ν hP F hF hinv _ hρ₀).2.2,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    simp only [mul_toReal]
    rw [integral_const_mul]
    push_cast
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotMap
section
open MeasureTheory Topology
open scoped ENNReal

theorem UpperTheory.ConvolutionTheory.G.quotMap_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotMap := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP' e y hμ hν F hF hinv
  obtain ⟨ρ0, -, hρ, -⟩ := hN G' T' μ' j' ν' hP'
  set ρ : G' → ℝ≥0∞ := fun g => (ρ0 g : ℝ≥0∞) with hρdef
  have hjc : Continuous j := hP.2.1.continuous
  have hj'c : Continuous j' := hP'.2.1.continuous
  have hec : Continuous e := e.continuous_toFun
  have hejc : Continuous (fun t => e (j t)) := hec.comp hjc
  haveI := hP.2.2.1
  haveI := hP'.1.1
  haveI := hP'.1.2
  have hrange : ∀ t, e (j t) ∈ Set.range j' := by
    have hcl : IsClosed (Set.range j') := hP'.2.1.isClosed_range
    have ho : IsOpen (Set.range j')ᶜ := hcl.isOpen_compl
    have h0 : (ν.map (fun t => e (j t))) (Set.range j')ᶜ = 0 := by
      rw [hν, Measure.map_apply hj'c.measurable ho.measurableSet]
      have : j' ⁻¹' (Set.range j')ᶜ = ∅ := by
        ext t; simp
      rw [this, measure_empty]
    rw [Measure.map_apply hejc.measurable ho.measurableSet] at h0
    have he := (ho.preimage hejc).eq_empty_of_measure_zero h0
    intro t
    by_contra hc
    have : t ∈ (fun t => e (j t)) ⁻¹' (Set.range j')ᶜ := hc
    rw [he] at this
    exact this
  have hφ : Measurable (fun g : G => e g * y) := (hec.mul continuous_const).measurable
  have hF1 : Measurable (fun g => F (e g * y)) := hF.comp hφ
  have hinv1 : ∀ t g, (fun g => F (e g * y)) (j t * g) = (fun g => F (e g * y)) g := by
    intro t g
    obtain ⟨t', ht'⟩ := hrange t
    simp only [map_mul, ← ht', mul_assoc, hinv]
  have hρ1 : UpperTheory.ConvolutionTheory.G.IsNrm j ν (fun g => ρ (e g * y)) := by
    refine ⟨hρ.1.comp hφ, fun x => ?_⟩
    have hm : Measurable (fun z : G' => ρ (z * (e x * y))) := hρ.1.comp (measurable_mul_const _)
    have h1 := lintegral_map (μ := ν) hm hejc.measurable
    have h2 := lintegral_map (μ := ν') hm hj'c.measurable
    rw [hν, h2, hρ.2] at h1
    simp only [map_mul, mul_assoc]
    exact h1.symm
  haveI : μ'.IsMulRightInvariant := by
    have h : μ'.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  have hmp : MeasurePreserving (fun g : G => e g * y) μ μ' :=
    (measurePreserving_mul_right μ' y).comp ⟨hec.measurable, hμ⟩
  have hemb : MeasurableEmbedding (fun g : G => e g * y) :=
    (e.toHomeomorph.trans (Homeomorph.mulRight y)).measurableEmbedding
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP _ hF1 hinv1 _ hρ1
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F hF hinv ρ hρ
  refine ⟨?_, ?_⟩
  · rw [a1, b1]
    exact hmp.integrable_comp_emb hemb (g := fun x => F x * ((ρ x).toReal : ℂ))
  · rw [a3, b3]
    exact hmp.integral_comp hemb (fun x => F x * ((ρ x).toReal : ℂ))
end

