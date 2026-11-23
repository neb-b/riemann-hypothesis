module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideDescendsFinite
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx

theorem exists_bumps_inf : (∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ)))) → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∃ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ ∀ k, Integrable (fouInf ψ laminf (ρ k)) laminf := by
  intro hreal F _ _ hF ψ hψ laminf hH
  haveI := hF
  classical
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have he : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) := (GlobalTheory.CompanionTheory.SW.RealCoord.isHomeomorph_coord F).continuous
  have he' : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F).symm := (GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F).symm.continuous
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨a, ha, hχ⟩ := GlobalTheory.CompanionTheory.SW.SdPi.exists_form (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) he' (psiInf F ψ) hpc (fun _ => hψ.2.1 _)
    (fun u v => by
      simp only [psiInf, map_add (f := _), ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
    (_root_.GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).2.2
  obtain ⟨g, hg1, hg2, hg3⟩ := hreal (InfinitePlace F) a ha
  set e := GlobalTheory.CompanionTheory.SW.RealCoord.coord F with hedef
  set E := GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F with hEdef
  have hEe : ∀ y, E y = e y := fun _ => rfl
  haveI : (laminf.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map laminf e.toAddEquiv he he'
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, laminf.map e = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : laminf.map e = 0 := by simpa using hc
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := laminf.map e)).open_pos Set.univ isOpen_univ
      Set.univ_nonempty (by simp [h0])
  have hme : MeasurableEmbedding e := E.measurableEmbedding
  have hint : ∀ f : (InfinitePlace F → ℝ) → ℂ, ∫ y, f (e y) ∂laminf = (c : ℝ) • ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  have hintR : ∀ f : (InfinitePlace F → ℝ) → ℝ, ∫ y, f (e y) ∂laminf = (c : ℝ) * ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  refine ⟨fun k y => g k (e y), fun k => ⟨(hg1 k).1.comp he, (hg1 k).2.1.comp_homeomorph E, fun y => (hg1 k).2.2.1 _, ?_⟩, ?_, fun k => ?_⟩
  · rw [hintR]
    have : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc0
    exact mul_pos this (hg1 k).2.2.2
  · rw [Filter.tendsto_smallSets_iff]
    intro U hU
    have hV : E.symm ⁻¹' U ∈ nhds (0 : InfinitePlace F → ℝ) := by
      apply E.symm.continuous.continuousAt.preimage_mem_nhds
      have : E.symm 0 = 0 := e.symm.map_zero
      rwa [this]
    obtain ⟨ε, hε, hεV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    have hlim : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually (ge_mem_nhds hε)] with k hk y hy
    have h1 : e y ∈ tsupport (g k) := tsupport_comp_subset_preimage (g k) he hy
    have h3 : e y ∈ E.symm ⁻¹' U := hεV (Metric.closedBall_subset_closedBall hk (hg2 k h1))
    have h5 : E.symm (e y) = y := E.symm_apply_apply y
    rw [Set.mem_preimage, h5] at h3
    exact h3
  · have hfou : ∀ t, fouInf ψ laminf (fun y => g k (e y)) t = (c : ℝ) • ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ)) := by
      intro t
      have h6 := hint (fun u => (g k u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (u w * e t w) : ℝ) : ℂ)))
      rw [← h6, fouInf]
      simp only [hχ, map_mul, Pi.mul_apply]
    have hG : Integrable (fun t => ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ))) laminf := by
      have h7 : Integrable (fun t : InfinitePlace F → ℝ => ∫ x, (g k x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) (laminf.map e) := by
        rw [hc]
        exact (hg3 k).smul_measure_nnreal
      exact hme.integrable_map_iff.1 h7
    rw [funext hfou]
    exact hG.smul (c : ℝ)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralEqTsumFd
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs

section Gen

variable {V C : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup C] [Countable C]

def per (ι : C →+ V) (f : V → ℂ) (b : V) : ℂ := ∑' c, f (b + ι c)

def UnifSummable (ι : C →+ V) (f : V → ℂ) : Prop :=
  ∀ K : Set V, IsCompact K → ∃ u : C → ℝ, Summable u ∧ ∀ c : C, ∀ b ∈ K, ‖f (b + ι c)‖ ≤ u c

theorem continuous_per {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Continuous (per ι f) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨u, hu, hb⟩ := h K hK
  have : ContinuousOn (per ι f) K :=
    continuousOn_tsum (fun c => (hf.comp (continuous_id.add continuous_const)).continuousOn) hu
      (fun c b hb' => hb c b hb')
  exact this.continuousAt hxK

theorem per_add (ι : C →+ V) (f : V → ℂ) (x : V) (c : C) : per ι f (x + ι c) = per ι f x := by
  unfold per
  rw [← (Equiv.addLeft c).tsum_eq (fun d => f (x + ι d))]
  refine tsum_congr fun d => ?_
  simp [add_assoc]

theorem per_bounded {ι : C →+ V} {f : V → ℂ} (h : UnifSummable ι f) {K : Set V} (hK : IsCompact K)
    (hx : ∀ x, ∃ a, x - ι a ∈ K) : ∃ M, ∀ x, ‖per ι f x‖ ≤ M := by
  obtain ⟨u, hu, hb⟩ := h K hK
  refine ⟨∑' c, u c, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hx x
  have e : per ι f x = per ι f (x - ι a) := by
    rw [← per_add ι f (x - ι a) a, sub_add_cancel]
  rw [e]
  exact tsum_of_norm_bounded hu.hasSum fun c => hb c _ ha

theorem integrableOn_bdd {μ : Measure V} {D : Set V} (hD : μ D ≠ ∞) {g : V → ℂ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) : IntegrableOn g D μ :=
  Measure.integrableOn_of_bounded hD hg.aestronglyMeasurable (Filter.Eventually.of_forall hM)

theorem integrable_of_unif {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f)
    (μ : Measure V) [μ.IsAddHaarMeasure] {K : Set V} (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) :
    Integrable f μ := by
  obtain ⟨u, hu, hb⟩ := h K hK
  obtain ⟨k, hk⟩ : K.Nonempty := by
    obtain ⟨a, ha⟩ := hx 0
    exact ⟨_, ha⟩
  have hu0 : ∀ a, 0 ≤ u a := fun a => (norm_nonneg _).trans (hb a k hk)
  let s : C → TopologicalSpace.Compacts V := fun a =>
    ⟨(fun y => y + ι a) '' K, hK.image (continuous_id.add continuous_const)⟩
  let G : C(V, ℂ) := ⟨f, hf⟩
  have hs : ⋃ a, (s a : Set V) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := hx x
    exact ⟨a, x - ι a, ha, sub_add_cancel _ _⟩
  have hμ : ∀ a, μ.real (s a : Set V) = μ.real K := by
    intro a
    have : ((s a : TopologicalSpace.Compacts V) : Set V) = (fun y => y + -ι a) ⁻¹' K := by
      show (fun y => y + ι a) '' K = _
      rw [Set.image_add_right]
    rw [this, Measure.real, Measure.real, measure_preimage_add_right]
  have hn : ∀ a, ‖G.restrict (s a : Set V)‖ ≤ u a := by
    intro a
    rw [ContinuousMap.norm_le _ (hu0 a)]
    rintro ⟨y, b, hb', rfl⟩
    exact hb a b hb'
  refine integrable_of_summable_norm_restrict (f := G) (s := s) ?_ hs
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) measureReal_nonneg) (fun a => ?_)
    (hu.mul_right (μ.real K))
  rw [hμ]
  exact mul_le_mul_of_nonneg_right (hn a) measureReal_nonneg

theorem countable_range (ι : C →+ V) : Countable ι.range :=
  ι.rangeRestrict_surjective.countable

theorem summable_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    Summable fun c => ∫ x in D, ‖h (x + ι c)‖ ∂μ := by
  have := countable_range ι
  have hsum := hD.lintegral_eq_tsum'' (fun x => ‖h x‖ₑ)
  have hfin : ∑' g : ι.range, ∫⁻ x in D, ‖h (g +ᵥ x)‖ₑ ∂μ ≠ ∞ := by
    rw [← hsum]
    exact hh.2.ne
  have hs := ENNReal.summable_toReal hfin
  have h2 := ((ι.ofInjective hι).toEquiv.summable_iff).2 hs
  refine h2.congr fun c => ?_
  rw [integral_norm_eq_lintegral_enorm (hh.comp_add_right (ι c)).integrableOn.aestronglyMeasurable]
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [Function.comp, this]

theorem integral_eq_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x, h x ∂μ = ∑' c, ∫ x in D, h (x + ι c) ∂μ := by
  have := countable_range ι
  rw [hD.integral_eq_tsum'' h hh, ← (ι.ofInjective hι).toEquiv.tsum_eq]
  refine tsum_congr fun c => ?_
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [this]

theorem setIntegral_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x in D, ∑' c, h (x + ι c) ∂μ = ∫ x, h x ∂μ := by
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun c x => h (x + ι c))
    (fun c => (hh.comp_add_right (ι c)).integrableOn) (summable_fd hι hD hh)
  rw [integral_eq_tsum_fd hι hD hh]
  exact hs.tsum_eq.symm

theorem per_unfold {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {f e : V → ℂ} (hfi : Integrable f μ)
    (he : Continuous e) (hen : ∀ x, ‖e x‖ = 1) (hep : ∀ x c, e (x + ι c) = e x) :
    ∫ b in D, per ι f b * e b ∂μ = ∫ b, f b * e b ∂μ := by
  have hh : Integrable (fun b => f b * e b) μ :=
    hfi.mono (hfi.aestronglyMeasurable.mul he.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp [hen])
  rw [← setIntegral_tsum_fd hι hD hh]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show per ι f x * e x = ∑' c, f (x + ι c) * e (x + ι c)
  simp only [hep]
  exact tsum_mul_right.symm

def ser (a : C → ℂ) (E : C → V → ℂ) (b : V) : ℂ := ∑' t, a t * E t b

theorem continuous_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) : Continuous (ser a E) :=
  continuous_tsum (fun t => continuous_const.mul (hEc t)) ha (fun t b => by simp [hEn])

theorem norm_ser_le {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEn : ∀ t b, ‖E t b‖ = 1) (b : V) : ‖ser a E b‖ ≤ ∑' t, ‖a t‖ :=
  tsum_of_norm_bounded ha.hasSum fun t => by simp [hEn]

theorem coef_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) {μ : Measure V} {D : Set V}
    (hD1 : μ D = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0) (s : C) :
    ∫ x in D, ser a E x * E (-s) x ∂μ = a s := by
  classical
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  have hr : μ.real D = 1 := by simp [Measure.real, hD1]
  have hint : ∀ t, IntegrableOn (fun x => a t * E t x * E (-s) x) D μ := fun t =>
    integrableOn_bdd hDf ((continuous_const.mul (hEc t)).mul (hEc (-s))) (M := ‖a t‖)
      (fun x => by simp [hEn])
  have hn : ∀ t, ∫ x in D, ‖a t * E t x * E (-s) x‖ ∂μ = ‖a t‖ := fun t => by
    simp [hEn, hr]
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun t x => a t * E t x * E (-s) x) hint (by simpa only [hn] using ha)
  have hval : ∀ t, t ≠ s → ∫ x in D, a t * E t x * E (-s) x ∂μ = 0 := fun t ht => by
    simp only [mul_assoc]
    rw [integral_const_mul, horth s t ht, mul_zero]
  have hs1 : ∫ x in D, a s * E s x * E (-s) x ∂μ = a s := by
    simp only [mul_assoc, hself]
    simp [hr]
  have h1 := hasSum_single (f := fun t => ∫ x in D, a t * E t x * E (-s) x ∂μ) s
    (fun t ht => hval t ht)
  have h2 := hs.unique h1
  rw [hs1] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ser a E x * E (-s) x = ∑' t, a t * E t x * E (-s) x
  simp only [ser, tsum_mul_right]

theorem poisson_gen {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) (hD1 : μ D = 1) {K : Set V}
    (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) (hEp : ∀ t x c, E t (x + ι c) = E t x)
    (hE0 : ∀ t, E t 0 = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0)
    (hcomp : ∀ g : V → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in D, g b * E (-t) b ∂μ = 0) → ∀ x, g x = 0)
    {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Integrable f μ ∧ (Summable (fun t => ∫ b, f b * E (-t) b ∂μ) →
      ∑' c, f (ι c) = ∑' t, ∫ b, f b * E (-t) b ∂μ) := by
  have hfi := integrable_of_unif hf h μ hK hx
  refine ⟨hfi, fun hsum => ?_⟩
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  set a : C → ℂ := fun t => ∫ b, f b * E (-t) b ∂μ with hadef
  have ha : Summable fun t => ‖a t‖ := hsum.norm
  have hP := continuous_per hf h
  have hS := continuous_ser ha hEc hEn
  obtain ⟨M, hM⟩ := per_bounded h hK hx
  have hperS : ∀ x c, ser a E (x + ι c) = ser a E x := fun x c => by
    simp only [ser, hEp]
  have hz := hcomp (fun x => per ι f x - ser a E x) (hP.sub hS)
    (fun x c => by simp only [per_add, hperS]) (fun t => ?_) 0
  · have e1 : per ι f 0 = ∑' c, f (ι c) := by simp [per]
    have e2 : ser a E 0 = ∑' t, a t := by simp [ser, hE0]
    rw [← e1, ← e2]
    exact sub_eq_zero.1 hz
  · have i1 : IntegrableOn (fun b => per ι f b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hP.mul (hEc _)) (M := M) (fun x => by simpa [hEn] using hM x)
    have i2 : IntegrableOn (fun b => ser a E b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hS.mul (hEc _)) (M := ∑' t, ‖a t‖)
        (fun x => by simpa [hEn] using norm_ser_le ha hEn x)
    simp only [sub_mul]
    rw [integral_sub i1 i2, per_unfold hι hD hfi (hEc _) (hEn _) (hEp _),
      coef_ser ha hEc hEn hD1 hself horth t, sub_eq_zero]

end Gen

section Adelic

end Adelic
end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAnnihilatorSelfDualVolume
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem psiF_eq_one_of_int_of_vanish : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : Af F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) → (∀ v ∈ T, c v = 0) → psiF ψ c = 1 := by
  intro F _ _ ψ hψ
  classical
  have hcont : Continuous (psiF ψ) := by
    have h : Continuous (fun y : Af F => ψ ((0 : InfiniteAdeleRing F), y)) :=
      hψ.1.comp (continuous_const.prodMk continuous_id)
    exact h
  have hW : psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (0 : Af F) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [psiF_zero]
    exact Metric.ball_mem_nhds _ (by norm_num)
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hc : Continuous (RestrictedProduct.structureMap R A Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) ∈
      nhds (fun v => (0 : A v)) :=
    hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hp
  obtain ⟨I, hI, t, ht, hsub⟩ := hp
  refine ⟨hI.toFinset, fun c hint hT => ?_⟩
  let H : AddSubgroup (Af F) :=
    { carrier := {y | (∀ v, y v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ hI.toFinset, y v = 0}
      add_mem' := by
        intro a b ha hb
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change a v + b v ∈ v.adicCompletionIntegers F
          exact add_mem (ha.1 v) (hb.1 v)
        · change a v + b v = 0
          rw [ha.2 v hv, hb.2 v hv, add_zero]
      zero_mem' := ⟨fun v => zero_mem _, fun v _ => rfl⟩
      neg_mem' := by
        intro a ha
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change -(a v) ∈ v.adicCompletionIntegers F
          exact neg_mem (ha.1 v)
        · change -(a v) = 0
          rw [ha.2 v hv, neg_zero] }
  have hs : ∀ y ∈ H, ‖psiF ψ y - 1‖ < 1 / 2 := by
    intro y hy
    have hmem : (fun v => (⟨y v, hy.1 v⟩ : A v)) ∈
        (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) := by
      refine hsub fun v hv => ?_
      have h0 : (⟨y v, hy.1 v⟩ : A v) = (0 : A v) :=
        Subtype.ext (hy.2 v (by simpa using hv))
      rw [h0]
      exact mem_of_mem_nhds (ht v)
    have he : RestrictedProduct.structureMap R A Filter.cofinite (fun v => (⟨y v, hy.1 v⟩ : A v)) = y :=
      by ext v; rfl
    have h2 : psiF ψ y ∈ Metric.ball (1 : ℂ) (1 / 2) := by
      rw [← he]
      exact hmem
    rw [Metric.mem_ball, dist_eq_norm] at h2
    exact h2
  exact char_eq_one_of_near H (psiF ψ) (psiF_zero ψ) (psiF_add ψ) hs (x := c) ⟨hint, hT⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalisedFourierBumpLimit
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim

theorem tendsto_fouInf_div_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∀ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets → ∀ t : Ainf F, Filter.Tendsto (fun k => fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) Filter.atTop (nhds 1) := by
  intro F _ _ ψ hψ laminf _ ρ hρ hsupp t
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hg_cont : Continuous fun x : Ainf F => psiInf F ψ (x * t) := by
    have h1 : Continuous fun x : Ainf F => pairA F (x * t) 0 :=
      (continuous_mul_const t).prodMk continuous_const
    exact hψ.1.comp h1
  have hg0 : psiInf F ψ (0 * t) = 1 := by
    have h0 : pairA F (0 * t) 0 = 0 := by
      rw [zero_mul]
      rfl
    show ψ (pairA F (0 * t) 0) = 1
    rw [h0, AddChar.map_zero_eq_one]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU : (fun x : Ainf F => psiInf F ψ (x * t)) ⁻¹' Metric.ball 1 (ε / 2) ∈ nhds (0 : Ainf F) := by
    apply hg_cont.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact Metric.ball_mem_nhds _ (half_pos hε)
  filter_upwards [Filter.tendsto_smallSets_iff.1 hsupp _ hU] with k hk
  obtain ⟨hc, hcs, hnn, hI⟩ := hρ k
  have hint : Integrable (ρ k) laminf := hc.integrable_of_hasCompactSupport hcs
  have hc1 : Continuous fun x => (ρ k x : ℂ) := Complex.continuous_ofReal.comp hc
  have hcs1 : HasCompactSupport fun x => (ρ k x : ℂ) := hcs.comp_left Complex.ofReal_zero
  have hi1 : Integrable (fun x => (ρ k x : ℂ)) laminf := hc1.integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable (fun x => (ρ k x : ℂ) * psiInf F ψ (x * t)) laminf :=
    (hc1.mul hg_cont).integrable_of_hasCompactSupport
      (hcs1.mul_right (f' := fun x => psiInf F ψ (x * t)))
  have key : fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)
      = ∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf := by
    unfold fouInf
    rw [← integral_complex_ofReal, ← integral_sub hi2 hi1]
    congr 1
    ext x
    ring
  have hIc : ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hI.ne'
  have hsplit : fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) - 1
      = (fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) := by
    rw [sub_div, div_self hIc]
  have hbound : ‖∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf‖ ≤ ∫ x, ρ k x * (ε / 2) ∂laminf := by
    apply norm_integral_le_of_norm_le (hint.mul_const _)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    by_cases hx : x ∈ tsupport (ρ k)
    · have h := hk hx
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_left h.le (hnn x)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [integral_mul_const] at hbound
  rw [dist_eq_norm, hsplit, key, norm_div, Complex.norm_real, Real.norm_of_nonneg hI.le, div_lt_iff₀ hI]
  nlinarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim
end
end

