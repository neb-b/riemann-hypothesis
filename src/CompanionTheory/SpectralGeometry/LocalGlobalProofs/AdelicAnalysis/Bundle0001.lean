module

public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingStableRangeOne
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleStableRange

theorem local_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, (t = 0 ∨ t = 1) ∧ a + t * b ≠ 0 ∧
      (w a ≤ 1 → w b ≤ 1 → w x ≤ 1 → w y ≤ 1 → w (a + t * b) = 1) := by
  have hb0 : a = 0 → b ≠ 0 := by
    rintro rfl rfl
    simp at h
  by_cases hint : w a ≤ 1 ∧ w b ≤ 1 ∧ w x ≤ 1 ∧ w y ≤ 1
  · obtain ⟨ha, hb, hx, hy⟩ := hint
    by_cases ha1 : w a = 1
    · refine ⟨0, Or.inl rfl, ?_, ?_⟩
      · intro h0
        have : a = 0 := by simpa using h0
        rw [this, map_zero] at ha1
        exact zero_ne_one ha1
      · intro _ _ _ _
        simpa using ha1
    · have hlt : w a < 1 := lt_of_le_of_ne ha ha1
      have hxa : w (x * a) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) hlt
      have hyb : w (y * b) = 1 := by
        have h1 : y * b = 1 + (-(x * a)) := by linear_combination h
        rw [h1, Valuation.map_add_eq_of_lt_left w (by rw [Valuation.map_neg, map_one]; exact hxa),
          map_one]
      have hb1 : w b = 1 := by
        refine le_antisymm hb ?_
        rw [map_mul] at hyb
        rw [← hyb]
        exact mul_le_of_le_one_left' hy
      have hab : w (a + 1 * b) = 1 := by
        rw [one_mul, Valuation.map_add_eq_of_lt_right w (by rw [hb1]; exact hlt), hb1]
      refine ⟨1, Or.inr rfl, ?_, fun _ _ _ _ => hab⟩
      intro h0
      rw [h0, map_zero] at hab
      exact zero_ne_one hab
  · by_cases ha0 : a = 0
    · refine ⟨1, Or.inr rfl, ?_, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hint⟩
      simpa [ha0] using hb0 ha0
    · refine ⟨0, Or.inl rfl, by simpa using ha0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hint⟩

theorem local_field {K : Type*} [Field K] (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, IsUnit (a + t * b) := by
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    rw [isUnit_iff_ne_zero, ha]
    rintro h0
    have hb : b = 0 := by simpa using h0
    simp [ha, hb] at h
  · exact ⟨0, by simpa [isUnit_iff_ne_zero] using ha⟩

theorem finite_part (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (a b : FiniteAdeleRing R K) (hab : IsCoprime a b) :
    ∃ t : FiniteAdeleRing R K, IsUnit (a + t * b) := by
  obtain ⟨x, y, hxy⟩ := hab
  have hloc : ∀ v : HeightOneSpectrum R, x v * a v + y v * b v = 1 := fun v =>
    congrArg (fun z : FiniteAdeleRing R K => z v) hxy
  choose e he hne hval using fun v : HeightOneSpectrum R =>
    local_val (Valued.v : Valuation (v.adicCompletion K) _) (a v) (b v) (x v) (y v) (hloc v)
  have hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K := by
    intro v
    rcases he v with h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
  let E : FiniteAdeleRing R K := ⟨e, Filter.Eventually.of_forall hint⟩
  refine ⟨E, ?_⟩
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun v h0 => hne v h0, ?_⟩
  filter_upwards [a.2, b.2, x.2, y.2] with v h1 h2 h3 h4
  exact hval v h1 h2 h3 h4

theorem infinite_part (K : Type*) [Field K] [NumberField K] (a b : InfiniteAdeleRing K)
    (hab : IsCoprime a b) : ∃ t : InfiniteAdeleRing K, IsUnit (a + t * b) := by
  obtain ⟨x, y, hxy⟩ := hab
  have hloc : ∀ v : InfinitePlace K, x v * a v + y v * b v = 1 := fun v =>
    congrArg (fun z : InfiniteAdeleRing K => z v) hxy
  choose t ht using fun v : InfinitePlace K => local_field (a v) (b v) (x v) (y v) (hloc v)
  exact ⟨t, Pi.isUnit_iff.2 ht⟩

theorem adeleRing_stableRange_one : ∀ (F : Type) [Field F] [NumberField F] (a b : AdeleRing (𝓞 F) F),
    IsCoprime a b → ∃ t, IsUnit (a + t * b) := by
  intro F _ _ a b hab
  obtain ⟨x, y, hxy⟩ := hab
  obtain ⟨t₁, u₁⟩ := infinite_part F a.1 b.1 ⟨x.1, y.1, congrArg Prod.fst hxy⟩
  obtain ⟨t₂, u₂⟩ := finite_part (𝓞 F) F a.2 b.2 ⟨x.2, y.2, congrArg Prod.snd hxy⟩
  exact ⟨(t₁, t₂), Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩

end GlobalTheory.CompanionTheory.AdeleStableRange
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactPartClosedOrbit
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem compact_part_closed_orbit :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] (V : Type) [TopologicalSpace V]
      [T2Space V] [LocallyCompactSpace V] (a : G → V → V),
      (Continuous fun p : G × V => a p.1 p.2) → (∀ y, a 1 y = y) →
      (∀ g h y, a (g * h) y = a g (a h y)) →
      ∀ (Z : Set V) (x : V), IsClosed Z → (∀ y, y ∈ Z ↔ ∃ g, a g x = y) →
      ∀ Ω : Set V, IsCompact Ω → ∃ C : Set G, IsCompact C ∧ ∀ y ∈ Ω, y ∈ Z → ∃ c ∈ C, a c x = y := by
  intro G _ _ _ _ _ _ V _ _ _ a ha h1 hmul Z x hZ hZx Ω hΩ
  have hmem : ∀ (g : G) (z : Z), a g z ∈ Z := by
    intro g z
    obtain ⟨h, hh⟩ := (hZx z).1 z.2
    exact (hZx _).2 ⟨g * h, by rw [hmul, hh]⟩
  letI : MulAction G Z :=
    { smul := fun g z => ⟨a g z, hmem g z⟩
      one_smul := fun z => Subtype.ext (h1 z)
      mul_smul := fun g h z => Subtype.ext (hmul g h z) }
  haveI : ContinuousSMul G Z :=
    ⟨Continuous.subtype_mk
      (ha.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      (fun p => hmem p.1 p.2)⟩
  haveI : MulAction.IsPretransitive G Z := by
    refine ⟨fun z w => ?_⟩
    obtain ⟨g, hg⟩ := (hZx z).1 z.2
    obtain ⟨h, hh⟩ := (hZx w).1 w.2
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    show a (h * g⁻¹) z = w
    rw [← hg, ← hmul, inv_mul_cancel_right, hh]
  haveI : LocallyCompactSpace Z := hZ.locallyCompactSpace
  haveI : BaireSpace Z := BaireSpace.of_t2Space_locallyCompactSpace
  have hx : x ∈ Z := (hZx x).2 ⟨1, h1 x⟩
  have hopen := isOpenMap_smul_of_sigmaCompact (G := G) (X := Z) ⟨x, hx⟩
  choose K hK hKn using fun g : G => exists_compact_mem_nhds g
  have hS : IsCompact ((Subtype.val : Z → V) ⁻¹' Ω) :=
    hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hΩ
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun g => (fun h : G => h • (⟨x, hx⟩ : Z)) '' interior (K g))
    (fun g => hopen _ isOpen_interior) (by
      intro z _
      obtain ⟨g, hg⟩ := (hZx z).1 z.2
      exact Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hKn g), Subtype.ext hg⟩)
  refine ⟨⋃ g ∈ t, K g, t.isCompact_biUnion fun g _ => hK g, ?_⟩
  intro y hyΩ hyZ
  have hy := ht (show (⟨y, hyZ⟩ : Z) ∈ (Subtype.val : Z → V) ⁻¹' Ω from hyΩ)
  rw [Set.mem_iUnion₂] at hy
  obtain ⟨g, hgt, c, hc, hcy⟩ := hy
  exact ⟨c, Set.mem_biUnion hgt (interior_subset hc), congrArg Subtype.val hcy⟩

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsCompactForMeasurePreservingEndos
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem lattice_pigeonhole_measure_preserving :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ →
      ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C →
        (∀ y, ∃ l, y - j l ∈ C) →
        ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ →
          ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by
  intro V _ _ _ _ _ _ _ _ μ _ htop Λ _ _ j C hC hcov
  have hCfin : μ C < ⊤ := hC.measure_lt_top
  obtain ⟨K, -, hKc, hK⟩ :=
    isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C) (by rw [htop]; exact hCfin)
  refine ⟨(fun p : V × V => p.1 - p.2) '' (K ×ˢ K),
    (hKc.prod hKc).image (continuous_fst.sub continuous_snd), fun e he hμ => ?_⟩
  by_contra hno
  push_neg at hno
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hem : Measurable e := he.measurable
  have hAm : MeasurableSet (e ⁻¹' K) := hem hKm
  have hμA : μ (e ⁻¹' K) = μ K := by
    have h := Measure.map_apply (μ := μ) hem hKm
    rw [hμ] at h
    exact h.symm

  let S : Λ → Set V := fun l => ((fun x => x + j l) ⁻¹' (e ⁻¹' K)) ∩ C
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hSm : ∀ l, MeasurableSet (S l) := fun l =>
    (hAm.preimage (measurable_add_const (j l))).inter hCm
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro l l' hll
    refine Set.disjoint_left.2 ?_
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    have hne : l - l' ≠ 0 := sub_ne_zero.2 hll
    refine hno _ hne ?_
    have hx1 : e (x + j l) ∈ K := hx
    have hx2 : e (x + j l') ∈ K := hx'
    have : e (j (l - l')) = e (x + j l) - e (x + j l') := by
      rw [← map_sub, map_sub j]
      congr 1
      abel
    rw [this]
    exact ⟨(e (x + j l), e (x + j l')), ⟨hx1, hx2⟩, rfl⟩
  have hcover : e ⁻¹' K ⊆ ⋃ l, (e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C) := by
    intro y hy
    obtain ⟨l, hl⟩ := hcov y
    exact Set.mem_iUnion.2 ⟨l, hy, hl⟩
  have hpiece : ∀ l, μ ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) = μ (S l) := by
    intro l
    have hS : S l = (fun x => x + j l) ⁻¹' ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := by
      ext x
      simp [S]
    rw [hS, measure_preimage_add_right]
  have hle : μ K ≤ μ C := by
    calc μ K = μ (e ⁻¹' K) := hμA.symm
      _ ≤ μ (⋃ l, (e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := measure_mono hcover
      _ ≤ ∑' l, μ ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := measure_iUnion_le _
      _ = ∑' l, μ (S l) := by simp_rw [hpiece]
      _ = μ (⋃ l, S l) := (measure_iUnion hdisj hSm).symm
      _ ≤ μ C := measure_mono (Set.iUnion_subset fun l => Set.inter_subset_right)
  exact absurd hK (not_lt.2 hle)

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatticeUnimod

theorem unimodular_of_isFundamentalDomain :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G),
      IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ →
        μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ 𝓕 h𝓕 hfin
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hmap : ∀ g : G, μ.map (· * g) = μ := by
    intro g
    have hc : μ.map (· * g) = Measure.haarScalarFactor (μ.map (· * g)) μ • μ :=
      Measure.isMulLeftInvariant_eq_smul _ _
    have hF : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hm : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := hF.measure_eq h𝓕
    have e1 : (μ.map (· * g)) 𝓕 = μ ((· * g) ⁻¹' 𝓕) :=
      (MeasurableEquiv.mulRight g).map_apply 𝓕
    have e2 : ((Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0) : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
      have e3 := congrArg (fun m : Measure G => m 𝓕) hc
      simp only [Measure.smul_apply] at e3
      rw [e1, hm] at e3
      rw [one_mul]
      exact e3.symm
    have e4 := (ENNReal.mul_left_inj h0 hfin.ne).1 e2
    have e5 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1 := ENNReal.coe_eq_one.1 e4
    rw [e5, one_smul] at hc
    exact hc
  haveI hR : μ.IsMulRightInvariant := ⟨hmap⟩
  refine ⟨h0, hR, ⟨?_⟩⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hVpos : 0 < μ V := Measure.measure_pos_of_mem_nhds μ hV1
  have e : c ^ 2 * μ V = 1 ^ 2 * μ V := by
    conv_rhs => rw [μeq]
    simp
  have e2 : c ^ 2 = 1 ^ 2 := (ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e
  have e3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e2
  rw [hc, e3, one_smul]

end GlobalTheory.CompanionTheory.SW.LatticeUnimod
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GeomSumIntLe
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem geom_sum_int_le (D M : ℕ) (hD : 0 < D) (hM : 1 ≤ M) (x₀ C : ℝ) :
    ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * D * M := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-a) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max C 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact le_max_right _ _
  have hCK : C ≤ K := by rw [hK]; exact le_max_left _ _
  refine ⟨K * Real.exp (-a * x₀) / (1 - q), fun r hr => ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, n₀ = ⌈x₀ - Real.log r⌉ := ⟨_, rfl⟩
  have hn₀le : x₀ - Real.log r ≤ n₀ := by rw [hn₀]; exact Int.le_ceil _
  have hr2 : (0 : ℝ) < r ^ (2 * D) := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * r ^ (2 * D) * Real.exp (-a * n₀) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.exp_pos (-a * n₀); positivity

  have hsupp : Function.support (fun j : ℤ =>
      (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ))))) ⊆
      Set.range (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro j hj
    have hnot : ¬ ((j : ℝ) + Real.log r < x₀) := by
      intro h
      apply hj
      simp [h]
    have hge : n₀ ≤ j := by
      rw [hn₀]
      apply Int.ceil_le.mpr
      linarith [not_lt.mp hnot]
    refine ⟨(j - n₀).toNat, ?_⟩
    have : (((j - n₀).toNat : ℕ) : ℤ) = j - n₀ := Int.toNat_of_nonneg (by omega)
    simp only [this]
    omega
  have hinj : Function.Injective (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro m n h
    simpa using h
  rw [← hinj.tsum_eq hsupp]

  have hterm : ∀ n : ℕ,
      (if (((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))) ≤
        ENNReal.ofReal (A * q ^ n) := by
    intro n
    split_ifs with h
    · simp
    · rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hr' : r ^ (2 * D) = Real.exp (((2 * D : ℕ) : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr]
      have hq' : q ^ n = Real.exp ((n : ℝ) * (-a)) := by
        rw [hq, Real.exp_nat_mul]
      have key : Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
          Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ))) =
          r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        rw [hr', hq', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ha]
        congr 1
        push_cast
        ring
      have hpos : 0 ≤ r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        have := Real.exp_pos (-a * n₀)
        positivity
      calc C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
            Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))
          = C * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) := by rw [mul_assoc, key]
        _ ≤ K * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) :=
            mul_le_mul_of_nonneg_right hCK hpos
        _ = A * q ^ n := by rw [hA]; ring
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hsum : Summable (fun n : ℕ => A * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left A
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

  have hexp : Real.exp (-a * n₀) ≤ Real.exp (-a * x₀) * r ^ (2 * D * M) := by
    have hr' : r ^ (2 * D * M) = Real.exp (((2 * D * M : ℕ) : ℝ) * Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr]
    rw [hr', ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : (((2 * D * M : ℕ) : ℝ)) = a := by rw [ha]; push_cast; ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_left hn₀le ha0.le]
  have hpow : r ^ (2 * D * (M + 1)) = r ^ (2 * D) * r ^ (2 * D * M) := by
    rw [← pow_add]
    congr 1
    ring
  have hAle : A ≤ K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1)) := by
    rw [hA, hpow]
    calc K * r ^ (2 * D) * Real.exp (-a * n₀)
        ≤ K * r ^ (2 * D) * (Real.exp (-a * x₀) * r ^ (2 * D * M)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K * Real.exp (-a * x₀) * (r ^ (2 * D) * r ^ (2 * D * M)) := by ring
  calc A * (1 - q)⁻¹
      ≤ (K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1))) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right hAle (inv_nonneg.mpr h1q.le)
    _ = K * Real.exp (-a * x₀) / (1 - q) * r ^ (2 * D * (M + 1)) := by
        rw [div_eq_mul_inv]; ring

theorem geom_sum_int :
    ∀ (D M : ℕ), 0 < D → 1 ≤ M → ∀ (x₀ C : ℝ), ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) :=
  fun D M hD hM x₀ C => geom_sum_int_le D M hD hM x₀ C

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AbsTprod

theorem multipliable_of_summable_abs_sub_one {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) : Multipliable a := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hm := multipliable_one_add_of_summable h'
  have hfun : (fun v => 1 + (a v - 1)) = a := funext fun v => by ring
  rwa [hfun] at hm

theorem tprod_nonneg_of_nonneg {ι : Type} {a : ι → ℝ} (hm : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v := by
  exact tprod_nonneg h0

theorem tprod_ne_zero_of_summable {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (h0 : ∀ v, a v ≠ 0) : ∏' v, a v ≠ 0 := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hne : ∀ v, 1 + (a v - 1) ≠ 0 := fun v => by simpa using h0 v
  have hp := tprod_one_add_ne_zero_of_summable (f := fun v => a v - 1) hne h'
  simpa using hp

theorem tprod_eq_prod_mul_tprod_compl {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (S : Finset ι) :
    Multipliable (fun v : {v // v ∉ S} => a v.1) ∧
      ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1 := by
  have hsub : ∀ p : ι → Prop, Multipliable (fun v : {v // p v} => a v.1) := fun p =>
    GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one (a := fun v : {v // p v} => a v.1)
      (h.comp_injective Subtype.val_injective)
  refine ⟨hsub _, ?_⟩
  have key := Multipliable.tprod_mul_tprod_compl (f := a) (s := (S : Set ι))
    (hsub (· ∈ (S : Set ι))) (hsub (· ∈ (S : Set ι)ᶜ))
  rw [← key, Finset.tprod_subtype']
  rfl

theorem abs_tprod : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  intro ι a h
  have hm := GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one h
  refine ⟨hm, fun S => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl h S, fun hpos => ?_,
    fun h0 => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm h0⟩
  exact lt_of_le_of_ne (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm fun v => (hpos v).le)
    (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable h fun v => (hpos v).ne').symm

end GlobalTheory.CompanionTheory.SW.AbsTprod
end

