module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise

namespace GlobalTheory.QuotientHaar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem measurable_translate (g : G) : Measurable (fun h : H => g * (h : G)) :=
  (continuous_const.mul continuous_subtype_val).measurable

noncomputable def cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] : G ⧸ H → Measure G :=
  Quotient.lift (fun g : G => ν.map (fun h : H => g * (h : G))) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h1 := map_mul_left_eq_self ν (⟨a⁻¹ * b, hab'⟩ : H)
    beta_reduce
    conv_lhs => rw [← h1]
    rw [Measure.map_map (measurable_translate H a) (measurable_const_mul _)]
    congr 1
    funext h
    simp [← mul_assoc])

theorem cosetMeasure_mk (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) :
    cosetMeasure H ν (g : G ⧸ H) = ν.map (fun h : H => g * (h : G)) := rfl

theorem cosetMeasure_apply (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) {s : Set G}
    (hs : MeasurableSet s) :
    cosetMeasure H ν (g : G ⧸ H) s = ν ((fun h : H => g * (h : G)) ⁻¹' s) := by
  rw [cosetMeasure_mk, Measure.map_apply (measurable_translate H g) hs]

theorem lintegral_cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞}
    (hf : Measurable f) (q : G ⧸ H) :
    ∫⁻ x, f x ∂(cosetMeasure H ν q) = fibreIntegral H ν f q := by
  induction q using QuotientGroup.induction_on with
  | H g => rw [cosetMeasure_mk, lintegral_map hf (measurable_translate H g), fibreIntegral_mk]

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem cosetMeasure_lt_top (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure]
    (q : G ⧸ H) {K : Set G} (hK : IsCompact K) : cosetMeasure H ν q K < ⊤ := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cosetMeasure_apply H ν g hK.measurableSet]
    have h1 : IsCompact ((fun x : G => g * x) ⁻¹' K) :=
      (Homeomorph.mulLeft g).isCompact_preimage.mpr hK
    exact (hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1).measure_lt_top

theorem measurable_cosetMeasure_open (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {U : Set G}
    (hU : IsOpen U) : Measurable (fun q : G ⧸ H => cosetMeasure H ν q U) := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : ν.Regular := inferInstance
  refine measurable_of_Ioi fun c => IsOpen.measurableSet ?_
  rw [← (QuotientGroup.isQuotientMap_mk H).isOpen_preimage, isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν g hU.measurableSet] at hg
  have hO : IsOpen ((fun h : H => g * (h : G)) ⁻¹' U) :=
    hU.preimage (continuous_const.mul continuous_subtype_val)
  obtain ⟨K, hKU, hK, hc⟩ := hO.exists_lt_isCompact hg
  have hev : ∀ᶠ x in nhds g, ∀ h ∈ K, x * (h : G) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun h hh => ?_
    have hcont : Continuous (fun p : G × H => p.1 * (p.2 : G)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (hU.mem_nhds (hKU hh))
  filter_upwards [hev] with x hx
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν x hU.measurableSet]
  exact hc.trans_le (measure_mono fun h hh => hx h hh)

theorem measurable_cosetMeasure (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] :
    Measurable (cosetMeasure H ν) := by
  let K := CompactExhaustion.choice G
  have hres : ∀ n, Measurable (fun q => (cosetMeasure H ν q).restrict (interior (K n))) := by
    intro n
    haveI : ∀ q, IsFiniteMeasure ((cosetMeasure H ν q).restrict (interior (K n))) := fun q =>
      isFiniteMeasure_restrict.mpr ((measure_mono interior_subset).trans_lt
        (cosetMeasure_lt_top H hH ν q (K.isCompact n))).ne
    have key : ∀ s : Set G, IsOpen s →
        Measurable fun q => (cosetMeasure H ν q).restrict (interior (K n)) s := by
      intro s hs
      simp only [Measure.restrict_apply hs.measurableSet]
      exact measurable_cosetMeasure_open H hH ν (hs.inter isOpen_interior)
    exact Measurable.measure_of_isPiSystem (S := {s : Set G | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen key (key _ isOpen_univ)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hmono : Monotone fun n => s ∩ interior (K n) := fun a b hab =>
    Set.inter_subset_inter_right _ (interior_mono (K.subset hab))
  have hun : ⋃ n, s ∩ interior (K n) = s := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, h, K.subset_interior_succ n hn⟩
  have : (fun q => cosetMeasure H ν q s) =
      fun q => ⨆ n, (cosetMeasure H ν q).restrict (interior (K n)) s := by
    funext q
    simp only [Measure.restrict_apply hs]
    rw [← hmono.measure_iUnion, hun]
  rw [this]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hres n)

theorem measurable_fibreIntegral (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {f : G → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreIntegral H ν f) := by
  have : fibreIntegral H ν f = fun q => ∫⁻ x, f x ∂(cosetMeasure H ν q) :=
    funext fun q => (lintegral_cosetMeasure H ν hf q).symm
  rw [this]
  exact (Measure.measurable_lintegral hf).comp (measurable_cosetMeasure H hH ν)

theorem quotientFormula_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H)) :
    QuotientFormula H (μ.bind (cosetMeasure H ν)) ν μ := by
  intro f hf
  refine ⟨measurable_fibreIntegral H hH ν hf, ?_⟩
  rw [Measure.lintegral_bind (measurable_cosetMeasure H hH ν).aemeasurable hf.aemeasurable]
  exact lintegral_congr fun q => lintegral_cosetMeasure H ν hf q

theorem isHaarMeasure_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) : (μ.bind (cosetMeasure H ν)).IsHaarMeasure := by
  haveI := hμ.finiteOnCompacts
  haveI := hμ.invariant
  have hm := measurable_cosetMeasure H hH ν
  haveI hfin : IsFiniteMeasureOnCompacts (μ.bind (cosetMeasure H ν)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.bind_apply hK.measurableSet hm.aemeasurable]
    have hC : ν (Subtype.val ⁻¹' (K⁻¹ * K)) < ⊤ :=
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)).measure_lt_top
    have hπ : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K) :=
      hK.image QuotientGroup.continuous_mk
    have hle : ∀ q, cosetMeasure H ν q K ≤ ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
        (fun _ => ν (Subtype.val ⁻¹' (K⁻¹ * K))) q := by
      intro q
      by_cases hq : q ∈ (QuotientGroup.mk : G → G ⧸ H) '' K
      · rw [Set.indicator_of_mem hq]
        obtain ⟨k, hk, rfl⟩ := hq
        rw [cosetMeasure_apply H ν k hK.measurableSet]
        refine measure_mono fun h hh => ?_
        exact ⟨k⁻¹, Set.inv_mem_inv.mpr hk, k * h, hh, by simp⟩
      · induction q using QuotientGroup.induction_on with
        | H g =>
          rw [cosetMeasure_apply H ν g hK.measurableSet]
          have : (fun h : H => g * (h : G)) ⁻¹' K = ∅ :=
            Set.eq_empty_of_forall_notMem fun h hh => hq ⟨g * h, hh, by simp⟩
          simp [this]
    refine (lintegral_mono hle).trans_lt ((lintegral_indicator_const_le _ _).trans_lt ?_)
    exact ENNReal.mul_lt_top hC hπ.measure_lt_top
  haveI hinv : (μ.bind (cosetMeasure H ν)).IsMulLeftInvariant := by
    refine (forall_measure_preimage_mul_iff _).mp fun a s hs => ?_
    rw [Measure.bind_apply hs hm.aemeasurable,
      Measure.bind_apply (measurable_const_mul a hs) hm.aemeasurable]
    have h1 : Measurable fun q => cosetMeasure H ν q s := (Measure.measurable_coe hs).comp hm
    have h2 := (measurePreserving_smul a μ).lintegral_comp h1
    rw [← h2]
    refine lintegral_congr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      change _ = cosetMeasure H ν ((a * g : G) : G ⧸ H) s
      rw [cosetMeasure_apply H ν g (measurable_const_mul a hs), cosetMeasure_apply H ν _ hs]
      congr 1
      ext h
      simp [mul_assoc]
  have hne : μ.bind (cosetMeasure H ν) ≠ 0 := by
    intro h0
    have h1 : μ.bind (cosetMeasure H ν) Set.univ = ν Set.univ * μ Set.univ := by
      rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable, ← lintegral_const]
      refine lintegral_congr fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H g => rw [cosetMeasure_apply H ν g MeasurableSet.univ, Set.preimage_univ]
    rw [h0] at h1
    exact mul_ne_zero (isOpen_univ.measure_ne_zero ν Set.univ_nonempty)
      (Measure.measure_univ_ne_zero.mpr hμ.ne_zero) h1.symm
  haveI : IsLocallyFiniteMeasure (μ.bind (cosetMeasure H ν)) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : NeZero (μ.bind (cosetMeasure H ν)) := ⟨hne⟩
  haveI : (μ.bind (cosetMeasure H ν)).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_regular
  exact {}

end GlobalTheory.QuotientHaar

namespace GlobalTheory.QuotientHaar

theorem existsUnique_haar_of_invariantRadon : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH ν _ μ hμ
  refine ⟨μ.bind (cosetMeasure H ν),
    ⟨isHaarMeasure_bind H hH ν μ hμ, quotientFormula_bind H hH ν μ⟩, fun dg hdg => ?_⟩
  ext s hs
  have hf : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (hdg.2 _ hf).2,
    (quotientFormula_bind H hH ν μ _ hf).2]

end GlobalTheory.QuotientHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemOfFiniteDimensionalSpanRightTranslates
section
open MeasureTheory

namespace GlobalTheory.UnitaryBC

theorem exists_finset_detecting_of_finiteDimensional {X : Type} (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] :
    ∃ s : Finset X, ∀ v : W, (∀ x ∈ s, (v : X → ℂ) x = 0) → v = 0 := by
  apply _root_.GlobalTheory.FinitePointsDetect.finite_points_detect

theorem exists_interpolation_of_finiteDimensional {X : Type} (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] :
    ∃ (s : Finset X) (w : s → X → ℂ), ∀ v ∈ W, ∀ y, v y = ∑ x : s, v x * w x y := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_detecting_of_finiteDimensional W
  let r : W →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun x : s => (LinearMap.proj (x : X)) ∘ₗ W.subtype
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hs v fun x hx => congrFun hv ⟨x, hx⟩
  obtain ⟨L, hL⟩ := r.exists_leftInverse_of_injective hr
  refine ⟨s, fun x => (L fun j => if x = j then 1 else 0 : W), fun v hv y => ?_⟩
  have h1 : L (r ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hL ⟨v, hv⟩
  rw [LinearMap.pi_apply_eq_sum_univ] at h1
  have h2 := congrFun (congrArg Subtype.val h1) y
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul] at h2
  exact h2.symm

theorem eq_zero_of_integral_mul_eq_zero_of_separating {K : Type} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (R : Subalgebra ℂ (K → ℂ))
    (hc : ∀ p ∈ R, Continuous p) (hs : ∀ p ∈ R, star p ∈ R)
    (hsep : ∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) (g : K → ℂ) (hg : Continuous g)
    (h0 : ∀ p ∈ R, ∫ k, g k * p k ∂μ = 0) : g = 0 := by
  let A : StarSubalgebra ℂ C(K, ℂ) :=
    { carrier := {φ | (φ : K → ℂ) ∈ R}
      mul_mem' := fun ha hb => R.mul_mem ha hb
      add_mem' := fun ha hb => R.add_mem ha hb
      algebraMap_mem' := fun c => R.algebraMap_mem c
      star_mem' := fun ha => hs _ ha }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨p, hp, hne⟩ := hsep x y hxy
    exact ⟨p, ⟨⟨p, hc p hp⟩, hp, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  let G : C(K, ℂ) := ⟨g, hg⟩
  have hcont : Continuous fun φ : C(K, ℂ) => ∫ k, g k * φ k ∂μ := by
    have h1 : Continuous fun φ : C(K, ℂ) =>
        ∫ k, (ContinuousMap.toLp (E := ℂ) 1 μ ℂ (G * φ)) k ∂μ :=
      MeasureTheory.continuous_integral.comp
        ((ContinuousMap.toLp (E := ℂ) 1 μ ℂ).continuous.comp (continuous_const.mul continuous_id))
    convert h1 using 2 with φ
    exact (integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ) μ (G * φ))).symm
  have hcl : IsClosed {φ : C(K, ℂ) | ∫ k, g k * φ k ∂μ = 0} := isClosed_eq hcont continuous_const
  have hmem : star G ∈ closure (A : Set C(K, ℂ)) := by
    have : star G ∈ A.topologicalClosure := htop ▸ StarSubalgebra.mem_top
    exact this
  have hsub : (A : Set C(K, ℂ)) ⊆ {φ : C(K, ℂ) | ∫ k, g k * φ k ∂μ = 0} :=
    fun φ hφ => h0 _ hφ
  have hz : ∫ k, g k * (starRingEnd ℂ) (g k) ∂μ = 0 := closure_minimal hsub hcl hmem
  simp only [Complex.mul_conj] at hz
  rw [integral_complex_ofReal] at hz
  have hz' : ∫ k, Complex.normSq (g k) ∂μ = 0 := by exact_mod_cast hz
  have hcn : Continuous fun k => Complex.normSq (g k) := Complex.continuous_normSq.comp hg
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (g k))
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hz'
  have := (Continuous.ae_eq_iff_eq μ hcn continuous_zero).1 hae
  funext k
  exact Complex.normSq_eq_zero.1 (congrFun this k)

theorem mem_of_finiteDimensional_span_rightTranslates :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (R : Subalgebra ℂ (K → ℂ)), (∀ p ∈ R, Continuous p) → (∀ p ∈ R, star p ∈ R) → (∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) → (∀ p ∈ R, ∃ (m : ℕ) (a b : Fin m → K → ℂ), (∀ i, a i ∈ R ∧ Continuous (b i)) ∧ ∀ x k, p (x⁻¹ * k) = ∑ i, a i x * b i k) → ∀ f : K → ℂ, Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k))) → f ∈ R := by
  intro K _ _ _ _ _ R hc hs hsep hsplit f hf hfd
  classical
  borelize K
  let μ : Measure K := Measure.haar
  have hint : ∀ u : K → ℂ, Continuous u → Integrable u μ := fun u hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfx : ∀ x : K, Continuous fun k => f (x * k) := fun x =>
    hf.comp (continuous_const.mul continuous_id)
  obtain ⟨s, w, hw⟩ := exists_interpolation_of_finiteDimensional
    (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k)))
  have hdec : ∀ y k, f (y * k) = ∑ x : s, f (x * k) * w x y := fun y k =>
    hw _ (Submodule.subset_span ⟨k, rfl⟩) y

  have hconv : ∀ p ∈ R, (fun y => ∫ k, f (y * k) * p k ∂μ) ∈ R := by
    intro p hp
    obtain ⟨m, a, b, hab, hp'⟩ := hsplit p hp
    have : (fun y => ∫ k, f (y * k) * p k ∂μ) = ∑ i, (∫ k, f k * b i k ∂μ) • a i := by
      funext y
      have h1 := integral_mul_left_eq_self (μ := μ) (fun k => f k * p (y⁻¹ * k)) y
      simp only [inv_mul_cancel_left] at h1
      rw [h1]
      simp only [hp', Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← integral_mul_const]
        congr 1
        funext k
        ring
      · intro i _
        exact hint _ (hf.mul (continuous_const.mul (hab i).2))
    rw [this]
    exact R.sum_mem fun i _ => R.smul_mem (hab i).1 _
  let T : R →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun p x => ∫ k, f (x * k) * (p : K → ℂ) k ∂μ
      map_add' := fun p q => by
        funext x
        simp only [Subalgebra.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ ((hfx x).mul (hc _ p.2))) (hint _ ((hfx x).mul (hc _ q.2)))
      map_smul' := fun c p => by
        funext x
        simp only [Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext k
        ring }
  have hmem : (fun x : s => f x) ∈ LinearMap.range T := by
    by_contra hne
    obtain ⟨l, hl1, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
    let c : s → ℂ := fun x => l fun j => if x = j then 1 else 0
    have hl : ∀ v : s → ℂ, l v = ∑ x, v x * c x := fun v => LinearMap.pi_apply_eq_sum_univ l v
    have hg : (fun k => ∑ x : s, f (x * k) * c x) = 0 := by
      refine eq_zero_of_integral_mul_eq_zero_of_separating μ R hc hs hsep _
        (continuous_finsetSum _ fun x _ => (hfx x).mul continuous_const) fun p hp => ?_
      have h1 : l (T ⟨p, hp⟩) = 0 := by
        have : l (T ⟨p, hp⟩) ∈ Submodule.map l (LinearMap.range T) :=
          Submodule.mem_map_of_mem ⟨_, rfl⟩
        rw [hl0] at this
        exact (Submodule.mem_bot ℂ).1 this
      rw [hl] at h1
      rw [← h1]
      simp only [Finset.sum_mul]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        change _ = (∫ k, f (x * k) * p k ∂μ) * c x
        rw [← integral_mul_const]
        congr 1
        funext k
        ring
      · intro x _
        exact hint _ (((hfx x).mul continuous_const).mul (hc p hp))
    apply hl1
    rw [hl]
    simpa using congrFun hg 1
  obtain ⟨p, hp⟩ := hmem
  have hfeq : f = fun y => ∫ k, f (y * k) * (p : K → ℂ) k ∂μ := by
    funext y
    have h1 := hdec y 1
    simp only [mul_one] at h1
    rw [h1]
    have h2 : ∀ k, f (y * k) * (p : K → ℂ) k = ∑ x : s, f (x * k) * (p : K → ℂ) k * w x y := by
      intro k
      rw [hdec y k, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [h2]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_mul_const]
      congr 1
      exact (congrFun hp x).symm
    · intro x _
      exact hint _ (((hfx x).mul (hc _ p.2)).mul continuous_const)
  rw [hfeq]
  exact hconv _ p.2

end GlobalTheory.UnitaryBC
end

