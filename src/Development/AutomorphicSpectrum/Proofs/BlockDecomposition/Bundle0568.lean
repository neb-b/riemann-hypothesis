module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedVolume
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.Lim

theorem tendsto_of_squeeze (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (t e : ℕ → ℝ) (L : ℝ)
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) (ht : Filter.Tendsto t Filter.atTop (nhds L))
    (hb : ∀ j, Filter.Tendsto (b j) Filter.atTop (nhds (t j)))
    (h1 : ∀ j k, b j k ≤ a k) (h2 : ∀ j k, a k ≤ b j k + e j) :
    Filter.Tendsto a Filter.atTop (nhds L) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ3 : 0 < δ / 3 := by positivity
  have e1 := he.eventually (Metric.ball_mem_nhds _ hδ3)
  have e2 := ht.eventually (Metric.ball_mem_nhds _ hδ3)
  obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
  have e3 := (hb j).eventually (Metric.ball_mem_nhds _ hδ3)
  filter_upwards [e3] with k hk
  rw [Real.dist_eq] at hj1 hj2 hk
  have p1 := abs_lt.1 hj1
  have p2 := abs_lt.1 hj2
  have p3 := abs_lt.1 hk
  have p4 := h1 j k
  have p5 := h2 j k
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem le_of_forall_mean_le {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [MeasurableSpace H]
    [OpensMeasurableSpace H] (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G : H → ℝ≥0∞) (hGc : Continuous fun y => (G y).toReal) (hGf : ∀ y, G y ≠ ⊤) (D : ℝ≥0)
    (hD : ∀ Y, MeasurableSet Y → ∫⁻ y in Y, G y ∂ν ≤ D * ν Y) (c : H) : G c ≤ D := by
  by_contra hlt
  have hlt' : (D : ℝ≥0∞) < G c := not_le.1 hlt
  have hr : (D : ℝ) < (G c).toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hGf c)).2 hlt'
    simpa using this
  obtain ⟨r, hr1, hr2⟩ := exists_between hr
  have hO : IsOpen {y | r < (G y).toReal} := isOpen_lt continuous_const hGc
  obtain ⟨K, hK, hcK, hKO⟩ := exists_compact_subset hO hr2
  have hYm : MeasurableSet (interior K) := isOpen_interior.measurableSet
  have hpos : ν (interior K) ≠ 0 := isOpen_interior.measure_ne_zero ν ⟨c, hcK⟩
  have hfin : ν (interior K) ≠ ⊤ := ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono interior_subset)
  have h1 : ENNReal.ofReal r * ν (interior K) ≤ ∫⁻ y in interior K, G y ∂ν := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hYm fun y hy => ?_
    have hy' : r < (G y).toReal := hKO (interior_subset hy)
    rw [← ENNReal.ofReal_toReal (hGf y)]
    exact ENNReal.ofReal_le_ofReal hy'.le
  have h2 := h1.trans (hD _ hYm)
  have hr0 : 0 ≤ r := (NNReal.coe_nonneg D).trans hr1.le
  have hnr : 0 < (ν (interior K)).toReal := ENNReal.toReal_pos hpos hfin
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0, ENNReal.coe_toReal] at h3
  exact absurd (le_of_mul_le_mul_right h3 hnr) (not_le.2 hr1)

end GlobalTheory.CompanionTheory.AvgFree.Lim


open GlobalTheory.CompanionTheory.AvgFree.Lim GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV in
theorem GlobalTheory.CompanionTheory.AvgFree.Lim.avg_tendsto_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : (HermR (Fv F v) σ n)) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → IsOpen A → ∀ Tt : ℕ → Set (Fin n → Fin M → (Fv F v ⊗[F] E)), Monotone Tt → (∀ j, IsCompact (Tt j) ∧ IsOpen (Tt j) ∧ Tt j ⊆ A ∧ Tt j ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X}) → A ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, Tt j → ∀ ε : ℕ → ℝ≥0, Filter.Tendsto ε Filter.atTop (nhds 0) → (∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y) ≤ ε j * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y) → mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : (HermR (Fv F v) σ n)) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : (HermR (Fv F v) σ n))).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv c A hAc hAo Tt hTm hT hcov ε hε hden
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, a9, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW n M
  haveI := hH n
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (HermR (Fv F v) σ n) := (a9 n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (HermR (Fv F v) σ n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have I := _root_.GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses F E σ hσ d b v lv hlv M J hJ n mv hmv
  have hAm : MeasurableSet A := hAo.measurableSet

  obtain ⟨h0m, -, -, C, hC⟩ := I (Tt 0) (hT 0).1 (hT 0).2.1 (hT 0).2.2.2
  have hsplit : ∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y →
      GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramIn (Fv F v) σ J Y) ≤
        GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (Tt j ∩ gramIn (Fv F v) σ J Y) +
          ε j * GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Y := by
    intro j Y hY
    refine (measure_mono ?_).trans ((measure_union_le (Tt j ∩ gramIn (Fv F v) σ J Y)
      ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y)).trans (by gcongr; exact hden j Y hY))
    intro X hX
    by_cases h : X ∈ Tt j
    · exact Or.inl ⟨h, hX.2⟩
    · exact Or.inr ⟨⟨hX.1, h⟩, hX.2⟩
  have hbd : ∀ j, mv c (Tt j) ≤ ((C + ε 0 : ℝ≥0) : ℝ≥0∞) := by
    intro j
    obtain ⟨hjm, hjc, hjf, -⟩ := I (Tt j) (hT j).1 (hT j).2.1 (hT j).2.2.2
    refine le_of_forall_mean_le (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (fun y => mv y (Tt j)) hjc hjf _
      (fun Y hY => ?_) c
    rw [← hjm Y hY]
    refine (measure_mono (Set.inter_subset_inter_left _ (hT j).2.2.1)).trans ((hsplit 0 Y hY).trans ?_)
    rw [h0m Y hY, ENNReal.coe_add, add_mul]
    gcongr
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hY fun y _ => hC y

  have hle : mv c A ≤ mv c (⋃ j, Tt j) := by
    have hcar := hmv.1 c
    refine (measure_mono (t := (⋃ j, Tt j) ∪ (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
      {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ) ?_).trans
      ((measure_union_le _ _).trans ?_)
    · intro X hX
      by_cases h : X ∈ (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
        {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})
      · exact Or.inl (hcov ⟨hX, h.2⟩)
      · exact Or.inr h
    · have hcar' : mv c (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
        {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ = 0 := hcar
      rw [hcar', add_zero]
  have hsup : mv c (⋃ j, Tt j) = ⨆ j, mv c (Tt j) := hTm.measure_iUnion
  have heq : mv c A = ⨆ j, mv c (Tt j) :=
    le_antisymm (hle.trans hsup.le) (iSup_le fun j => measure_mono (hT j).2.2.1)
  have hfin : mv c A ≠ ⊤ := by
    rw [heq]
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (iSup_le hbd)
  have hlim : Filter.Tendsto (fun j => mv c (Tt j)) Filter.atTop (nhds (mv c A)) := by
    rw [heq]
    exact tendsto_atTop_iSup fun i j hij => measure_mono (hTm hij)
  refine ⟨hfin, fun U hU hUt => ?_⟩

  have hinv := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  let Q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem (Fv F v) hinv hJ.1 X⟩
  have hQc : Continuous Q := (a10 n M J).subtype_mk _
  have hnear : ∀ W : Set (HermR (Fv F v) σ n), gramNear (Fv F v) σ J c W = (fun X => c - Q X) ⁻¹' W := by
    intro W
    ext X
    constructor
    · rintro ⟨u, hu, e⟩
      have : c - Q X = u := Subtype.ext e
      show c - Q X ∈ W
      rwa [this]
    · intro h
      exact ⟨c - Q X, h, rfl⟩
  let S : ℕ → Set (HermR (Fv F v) σ n) := fun k => (fun y => c - y) ⁻¹' U k
  have hgram : ∀ k, gramNear (Fv F v) σ J c (U k) = gramIn (Fv F v) σ J (S k) := by
    intro k
    rw [hnear]
    ext X
    constructor
    · intro h
      exact ⟨Q X, h, rfl⟩
    · rintro ⟨y, hy, e⟩
      have : y = Q X := Subtype.ext e.symm
      rw [this] at hy
      exact hy
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  have hSU : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) = GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k) := fun k =>
    (Measure.measurePreserving_sub_left _ c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) ≠ 0 := fun k =>
    (hSo k).measure_ne_zero _ ⟨c, hSc k⟩
  have htop : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : HermR (Fv F v) σ n => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : HermR (Fv F v) σ n => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk hs
    simpa using this
  have hAfin : ∀ B : Set (Fin n → Fin M → Fv F v ⊗[F] E), B ⊆ A → GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M B ≠ ⊤ :=
    fun B hB => ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono hB)
  refine ⟨fun k => ?_, ?_⟩
  · refine ⟨?_, hAfin _ Set.inter_subset_left⟩
    rw [hnear]
    exact (hAo.inter ((hU k).2.1.preimage (continuous_const.sub hQc))).measurableSet
  · refine tendsto_of_squeeze _
      (fun j k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (Tt j ∩ gramIn (Fv F v) σ J (S k))).toReal /
        (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal)
      (fun j => (mv c (Tt j)).toReal) (fun j => (ε j : ℝ)) _ ?_ ((ENNReal.tendsto_toReal hfin).comp hlim) ?_ ?_ ?_
    · have h := NNReal.tendsto_coe.2 hε
      rwa [NNReal.coe_zero] at h
    · intro j
      obtain ⟨hjm, hjc, hjf, -⟩ := I (Tt j) (hT j).1 (hT j).2.1 (hT j).2.2.2
      have key := tendsto_mean (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (fun y => mv y (Tt j)) c hjc.continuousAt
        (Filter.Eventually.of_forall hjf) S hSm hl hpos htop
      refine key.congr fun k => ?_
      rw [hSU k, hjm (S k) (hSm k)]
    · intro j k
      rw [hgram k]
      refine div_le_div_of_nonneg_right (ENNReal.toReal_mono (hAfin _ Set.inter_subset_left) ?_) ENNReal.toReal_nonneg
      exact measure_mono (Set.inter_subset_inter_left _ (hT j).2.2.1)
    · intro j k
      rw [hgram k]
      have hp : 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal := by
        rw [← hSU k]
        exact ENNReal.toReal_pos (hpos k) (htop k)
      have hs := hsplit j (S k) (hSm k)
      rw [hSU k] at hs
      have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAfin _ (Set.inter_subset_inter_left _ (hT j).2.2.1 |>.trans Set.inter_subset_left),
        ENNReal.mul_ne_top ENNReal.coe_ne_top (by rw [← hSU k]; exact htop k)⟩) hs
      rw [ENNReal.toReal_add (hAfin _ (Set.inter_subset_inter_left _ (hT j).2.2.1 |>.trans Set.inter_subset_left))
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (by rw [← hSU k]; exact htop k)), ENNReal.toReal_mul, ENNReal.coe_toReal] at hr
      rw [div_le_iff₀ hp, add_mul, div_mul_cancel₀ _ hp.ne']
      exact hr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingNormMeasure
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

section Ring

open scoped Pointwise

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A]

theorem map_mul_unit (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (u : Aˣ) :
    μ.map (fun x => (u : A) * x) = (distribHaarChar A u)⁻¹ • μ := by
  have hm : Measurable fun x : A => (u : A) * x := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun x : A => (u : A) * x) ⁻¹' B = u⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, map_inv]
  rfl

theorem exists_pos_finite (μ : Measure A) [μ.IsAddHaarMeasure] :
    ∃ K : Set A, μ K ≠ 0 ∧ μ K ≠ ∞ := by
  obtain ⟨K, hK, hn⟩ := exists_compact_mem_nhds (0 : A)
  refine ⟨K, ?_, hK.measure_lt_top.ne⟩
  exact (Measure.measure_pos_of_mem_nhds μ hn).ne'

theorem smul_inj (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have e := congrArg (fun m : Measure A => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem char_map (s : A ≃+* A) (hs : Continuous s) (hs' : Continuous s.symm) (u : Aˣ) :
    distribHaarChar A (Units.map (s : A →* A) u) = distribHaarChar A u := by
  let H : A ≃ₜ A := ⟨s.toEquiv, hs, hs'⟩
  let μ : Measure A := Measure.addHaar
  have : (μ.map H).IsAddHaarMeasure := s.toAddEquiv.isAddHaarMeasure_map μ hs hs'
  have : (μ.map H).Regular := Measure.Regular.map H
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have hap : ∀ S : Set A, (μ.map H) S = μ (H ⁻¹' S) := fun S =>
    H.toMeasurableEquiv.map_apply S
  have hpre : H ⁻¹' (H '' K) = K := H.injective.preimage_image K
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.map H) (s := H '' K)
    (by rwa [hap, hpre]) (by rwa [hap, hpre]) ?_
  rw [hap, hap, hpre, distribHaarChar_mul]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, hy⟩
    refine ⟨k, hk, H.injective ?_⟩
    rw [← hy]
    simp [H, Units.smul_def]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨H k, ⟨k, hk, rfl⟩, ?_⟩
    simp [H, Units.smul_def]

end Ring

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

theorem coordK_map_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  intro F E _ _ _ _ _ σ hσ d b v lam hlam c t w hc ht hnorm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, hsc, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set μ := coordK (Fv F v) b lam with hμ
  haveI : μ.Regular := inferInstance
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigma_sigma σ hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  let s : (Fv F v ⊗[F] E) ≃+* (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ, invFun := sigR (Fv F v) σ, left_inv := hss, right_inv := hss,
      map_mul' := map_mul _, map_add' := map_add _ }
  let u : (Fv F v ⊗[F] E)ˣ := hc.unit
  have hu : (u : Fv F v ⊗[F] E) = c := hc.unit_spec
  have hchar := char_map s hsc hsc u
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hqv : (qv v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by simp [qv]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero, hqv] at hnorm
    exact inv_ne_zero (pow_ne_zero w hq) hnorm.symm
  have hk : ‖t‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ w := by
    rw [hnorm, hqv, inv_pow]
  have h1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam t ht0 w hk
  have h2 := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam t ht0 _ h1
  have h3 := map_mul_unit μ (Units.map (s : _ →* _) u * u)
  have hval : ((Units.map (s : _ →* _) u * u : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t := by
    rw [ht, ← hu]
    rfl
  rw [hval, h2, map_mul, hchar] at h3
  have h4 := smul_inj μ h3
  have h5 : (distribHaarChar (Fv F v ⊗[F] E) u)⁻¹ = qv v ^ w := by
    refine (pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 ?_
    rw [inv_pow, pow_two]
    exact h4.symm
  rw [← h5, ← map_mul_unit μ u, hu]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSequenceNormBounds
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt.Normz

theorem norm_bounds_of_rec {F : Type*} [NormedField F] [IsUltrametricDist F] (w : ℕ → F) (p : F)
    (q : ℕ) (hq : 2 ≤ q) (hp : ‖p‖ < 1) (h0 : w 0 = 0) (h1 : w 1 ≠ 0)
    (hr : ∀ n, w (n + 1) ^ q + p * w (n + 1) = w n) :
    (∀ n, ‖w n‖ < 1) ∧ ∀ n, 2 ≤ n → ‖p‖ < ‖w n‖ := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  have hmax : ∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y => IsUltrametricDist.norm_add_le_max x y
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hlt : ∀ n, ‖w n‖ < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      by_contra hge
      rw [not_lt] at hge
      have hapos : 0 < ‖w (n + 1)‖ := lt_of_lt_of_le one_pos hge
      have hq1 : ‖w (n + 1)‖ ≤ ‖w (n + 1)‖ ^ (k + 2) := by
        calc ‖w (n + 1)‖ = ‖w (n + 1)‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖w (n + 1)‖ ^ (k + 2) := pow_le_pow_right₀ hge (by omega)
      have key : w (n + 1) ^ (k + 2) = w n + -(p * w (n + 1)) := by linear_combination hr n
      have h2 : ‖w (n + 1) ^ (k + 2)‖ ≤ max ‖w n‖ ‖-(p * w (n + 1))‖ := by
        rw [key]; exact hmax _ _
      rw [norm_pow, norm_neg, norm_mul] at h2
      have h3 : ‖p‖ * ‖w (n + 1)‖ < ‖w (n + 1)‖ ^ (k + 2) := by
        calc ‖p‖ * ‖w (n + 1)‖ < 1 * ‖w (n + 1)‖ := mul_lt_mul_of_pos_right hp hapos
          _ = ‖w (n + 1)‖ := one_mul _
          _ ≤ ‖w (n + 1)‖ ^ (k + 2) := hq1
      have h4 : ‖w n‖ < ‖w (n + 1)‖ ^ (k + 2) := lt_of_lt_of_le ih (le_trans hge hq1)
      exact absurd h2 (not_le.mpr (max_lt h4 h3))
  have hrec1 : w 1 ^ (k + 2) + p * w 1 = 0 := by
    have := hr 0
    rw [h0] at this
    exact this
  have hpw : w 1 ^ (k + 1) = -p := by
    have e : w 1 * (w 1 ^ (k + 1) + p) = 0 := by linear_combination hrec1
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h h1
    · linear_combination h
  have hnorm1 : ‖w 1‖ ^ (k + 1) = ‖p‖ := by rw [← norm_pow, hpw, norm_neg]
  have hp_pos : 0 < ‖p‖ := by
    rw [← hnorm1]
    exact pow_pos (norm_pos_iff.mpr h1) _
  have hw1 : ‖p‖ ≤ ‖w 1‖ := by
    rw [← hnorm1]
    calc ‖w 1‖ ^ (k + 1) ≤ ‖w 1‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hlt 1).le (by omega)
      _ = ‖w 1‖ := pow_one _
  have hsmall : ∀ a : F, ‖a‖ ≤ ‖p‖ → ‖a ^ (k + 2) + p * a‖ ≤ ‖p‖ ^ 2 := by
    intro a ha
    have ha0 : 0 ≤ ‖a‖ := norm_nonneg a
    refine le_trans (hmax _ _) (max_le ?_ ?_)
    · rw [norm_pow]
      calc ‖a‖ ^ (k + 2) ≤ ‖a‖ ^ 2 := pow_le_pow_of_le_one ha0 (ha.trans hp.le) (by omega)
        _ ≤ ‖p‖ ^ 2 := by gcongr
    · rw [norm_mul, sq]
      exact mul_le_mul_of_nonneg_left ha hp0
  have hstep : ∀ n, ‖p‖ ≤ ‖w n‖ → ‖p‖ < ‖w (n + 1)‖ := by
    intro n hn
    by_contra hc
    rw [not_lt] at hc
    have hb := hsmall (w (n + 1)) hc
    rw [hr n] at hb
    have hp2 : ‖p‖ ^ 2 < ‖p‖ := by
      rw [sq]
      calc ‖p‖ * ‖p‖ < 1 * ‖p‖ := mul_lt_mul_of_pos_right hp hp_pos
        _ = ‖p‖ := one_mul _
    linarith
  have hge : ∀ n, ‖p‖ ≤ ‖w (n + 1)‖ := by
    intro n
    induction n with
    | zero => exact hw1
    | succ n ih => exact (hstep _ ih).le
  refine ⟨hlt, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact hstep (m + 1) (hge m)

theorem norm_z_bounds : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → 2 ≤ qOf π → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) ∧ ∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖ := by
  intro l _ K χ π z hz hq hp
  obtain ⟨_, h0, h1, hr, _⟩ := hz
  have e : GlobalTheory.CompanionTheory.LTPer.Tilt.omC (((π : ↥K.1) : Om l)) = GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π := by
    rw [GlobalTheory.CompanionTheory.LTPer.Tilt.omC_apply, GlobalTheory.CompanionTheory.LTPer.Tilt.oc_apply]
  refine norm_bounds_of_rec (fun n => GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)) (GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π) (qOf π) hq hp
    (by simp [h0]) ?_ ?_
  · show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z 1) ≠ 0
    intro h
    have hn := congrArg norm h
    rw [GlobalTheory.CompanionTheory.LTPer.Tilt.norm_omC, norm_zero] at hn
    exact h1 (norm_eq_zero.mp hn)
  · intro n
    show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1)) ^ qOf π + GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π * GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1))
      = GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)
    have hr' : z (n + 1) ^ qOf π + ((π : ↥K.1) : Om l) * z (n + 1) = z n := hr n
    rw [← e, ← map_pow, ← map_mul, ← map_add (f := _), hr']

end GlobalTheory.CompanionTheory.LTPer.Tilt.Normz
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_theory_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → ∀ j : Fin (r + 1), j.val = 1 → Real.exp (s j) ≤ M * Real.exp (s 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound | exact GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound <;> assumption)
end

