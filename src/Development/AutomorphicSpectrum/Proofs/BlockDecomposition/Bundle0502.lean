module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem ae_lift_eq {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X} {fib : X → Measure V}
    (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι)
    (b : X) : ∀ᵐ x ∂(fib b), g x = b := by
  refine measure_mono_null ?_ (h.1 b)
  intro x hx hx'
  exact hx (hι ((hg x).symm.trans hx'.1))

theorem fibre_mass_on {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X}
    {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x))
    (hι : Function.Injective ι) (hgm : Measurable g) {A : Set V} {S : Set X} (hA : MeasurableSet A)
    (hS : MeasurableSet S) (hW : A ∩ g ⁻¹' S ⊆ W) :
    μ (A ∩ g ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  have hT : MeasurableSet (A ∩ g ⁻¹' S) := hA.inter (hgm hS)
  have e := h.2.1 ((A ∩ g ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [lintegral_indicator_one hT] at e
  rw [Measure.restrict_apply hT, Set.inter_eq_left.2 hW] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae := ae_lift_eq h hg hι b
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ g x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem avg_gen {V X Y : Type} {_ : TopologicalSpace V} {_ : MeasurableSpace V} {_ : TopologicalSpace X}
    {_ : MeasurableSpace X} {_ : AddCommGroup X} {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y}
    {W : Set V} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X}
    (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι) (hgc : Continuous g) (hV2 : T2Space V)
    (hVb : BorelSpace V) (hX2 : T2Space X) (hXb : BorelSpace X) (hXg : IsTopologicalAddGroup X)
    (hXl : LocallyCompactSpace X) (hXs : SecondCountableTopology X) (hμ : IsFiniteMeasureOnCompacts μ)
    (hν : ν.IsAddHaarMeasure) (hB : IsOpen B) (hWB : ∀ x, g x ∈ B → x ∈ W) {c : X} (hc : c ∈ B) {A : Set V}
    (hAc : IsCompact A) (hAo : IsOpen A) {U : ℕ → Set X} (hU : ∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : X) ∈ U k)
    (hUt : Filter.Tendsto U Filter.atTop (nhds (0 : X)).smallSets) :
    (∀ k, MeasurableSet (A ∩ {x | c - g x ∈ U k}) ∧ μ (A ∩ {x | c - g x ∈ U k}) ≠ ⊤) ∧
      Filter.Tendsto (fun k => (μ (A ∩ {x | c - g x ∈ U k})).toReal / (ν (U k)).toReal) Filter.atTop
        (nhds (fib c A).toReal) := by
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have hBc := hB.mem_nhds hc

  let S : ℕ → Set X := fun k => {s | c - s ∈ U k}
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  have hSU : ∀ k, ν (S k) = ν (U k) := fun k =>
    (Measure.measurePreserving_sub_left _ c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, ν (S k) ≠ 0 := fun k => (hSo k).measure_ne_zero _ ⟨c, hSc k⟩
  have htop : ∀ k, ν (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : X => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : X => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk (show c - s ∈ U k from hs)
    simpa using this

  obtain ⟨k0, hk0⟩ := (hl.eventually (Filter.eventually_smallSets_subset.2 hBc)).exists
  have hNc : IsCompact (S k0) := (Homeomorph.subLeft c).isCompact_preimage.2 (hU k0).1
  let A' : Set V := A ∩ g ⁻¹' S k0
  have hA'c : IsCompact A' := hAc.inter_right (hNc.isClosed.preimage hgc)
  have hA'o : IsOpen A' := hAo.inter ((hSo k0).preimage hgc)
  have hA'm : MeasurableSet A' := hA'o.measurableSet
  have hA'W : A' ⊆ W := fun x hx => hWB x (hk0 hx.2)

  let φ : V → ℝ := A'.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hA'o.frontier_eq, hA'c.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hA'c fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ W := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hA'c.isClosed) hA'W
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(fib s) = (fib s A').toReal := fun s => by
    simp [φ, integral_indicator hA'm, Measure.real]
  have hG : ContinuousAt (fun s => (fib s A').toReal) c := by
    have h := hC.continuousAt hBc
    simpa only [hint] using h
  have hfin : ∀ᶠ s in nhds c, fib s A' ≠ ⊤ := by
    filter_upwards [hBc] with s hs
    have h := hI s hs
    rw [integrable_indicator_iff hA'm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcv : fib c A' = fib c A := by
    refine measure_congr ?_
    filter_upwards [ae_lift_eq h hg hι c] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S k0
    rw [hx]
    exact hSc k0
  refine ⟨fun k => ?_, ?_⟩
  · have hO : IsOpen (A ∩ {x | c - g x ∈ U k}) := hAo.inter ((hSo k).preimage hgc)
    exact ⟨hO.measurableSet, ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono Set.inter_subset_left)⟩
  · have key := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.tendsto_mean ν (fun s => fib s A') c hG hfin S hSm hl hpos htop
    simp only [hcv] at key
    refine key.congr' ?_
    filter_upwards [hl.eventually (Filter.eventually_smallSets_subset.2 ((hSo k0).mem_nhds (hSc k0)))] with k hk
    have e : A ∩ {x | c - g x ∈ U k} = A' ∩ g ⁻¹' S k := by
      ext x
      exact ⟨fun h => ⟨⟨h.1, hk h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [hSU k, e, fibre_mass_on h hg hι hgc.measurable hA'm (hSm k) (fun x hx => hA'W hx.1)]

end GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k})).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ d b v lv hlv mv hmv c hc A hAc hAo U hU hUt
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b lv hlv.1
  obtain ⟨e1, e2, e3, e4, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Fv F v) n
  have hgc : Continuous (gramH hCM hJ (Fv F v) : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n) :=
    Continuous.subtype_mk (a10 n M J) _
  have hUo : IsOpen {r : Fv F v | IsUnit r} := by
    have : {r : Fv F v | IsUnit r} = {r | r ≠ 0} := by
      ext r
      simp [isUnit_iff_ne_zero]
    rw [this]
    exact isOpen_ne
  have hB : IsOpen {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} :=
    PI.VolStabS.isOpen_unitHerm (Fv F v) hUo σ n
  exact AvgV.avg_gen (q := gramR (Fv F v) σ J) (ι := Subtype.val) (g := gramH hCM hJ (Fv F v)) hmv
    (fun _ => rfl) Subtype.val_injective hgc inferInstance (a8 n M) e3 e4 inferInstance e1 e2
    (hW n M).toIsFiniteMeasureOnCompacts (hH n) hB (fun _ h => h) hc hAc hAo hU hUt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianHasBase
section
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.Base

theorem herm_add_left {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R} (hH : IsHerm c h)
    (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm, hH.add_right, map_add (f := _), ← hH.symm, ← hH.symm]

theorem herm_smul_left {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R} (hH : IsHerm c h)
    (a : R) (x z : V) : h (a • x) z = c a * h x z := by
  rw [hH.symm, hH.smul_right, map_mul, ← hH.symm]

theorem hasBase_of_field {k R : Type} [Field k] [CommRing R] [Algebra k R] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0)
    (hf : ∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) (hinv : ∀ a, c (c a) = a)
    (hfix : ∀ a, c a = a → ∃ x : k, algebraMap k R x = a)
    (hck : ∀ x : k, c (algebraMap k R x) = algebraMap k R x) (h𝔬 : ∀ a, a ∈ 𝔬 ↔ W a ≤ 1)
    (hWc : ∀ a, W (c a) = W a) (hW0 : ∀ a, W a = 0 → a = 0)
    (hN : ∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) : HasBase c 𝔬 := by
  unfold HasBase
  intro V _ _ _ h hH hP hiso L L' hL hL'
  have hanis : ∀ z : V, h z z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    have hex : ∃ y, h z y ≠ 0 := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      exact hne (hP.nondeg z hall)
    obtain ⟨y, hy⟩ := hex
    obtain ⟨b, hb⟩ := hf _ hy
    exact hiso z (b • y) hz (by rw [hH.smul_right, mul_comm]; exact hb)
  have key : ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 :=
    _root_.GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even c 𝔬 W hf hinv hfix hck h𝔬 hWc hW0 hN h hH hanis
  have h0 : ∀ x : V, h x 0 = 0 := fun x => by simpa using hH.smul_right 0 x 0
  let M : Submodule 𝔬 V :=
    { carrier := {z | ∃ a ∈ 𝔬, h z z = a + c a}
      add_mem' := by
        rintro z w ⟨a, ha, hz⟩ ⟨b, hb, hw⟩
        refine ⟨a + b + h z w, add_mem (add_mem ha hb) (key z w a b ha hb hz hw), ?_⟩
        rw [herm_add_left hH, hH.add_right, hH.add_right, hz, hw, hH.symm z w, map_add (f := _), map_add (f := _)]
        ring
      zero_mem' := ⟨0, zero_mem _, by rw [h0, map_zero, add_zero]⟩
      smul_mem' := by
        rintro r z ⟨a, ha, hz⟩
        refine ⟨c r * r * a, ?_, ?_⟩
        · have hr : W (r : R) ≤ 1 := (h𝔬 r).1 r.2
          rw [h𝔬, map_mul, map_mul, hWc]
          exact mul_le_one' (mul_le_one' hr hr) ((h𝔬 a).1 ha)
        · rw [Subring.smul_def, herm_smul_left hH, hH.smul_right, hz, map_mul, map_mul, hinv]
          ring }
  have hLM : ∀ N : Submodule 𝔬 V, IsEvenInt c 𝔬 h N → N ≤ M := by
    intro N hN' x hx
    unfold IsEvenInt at hN'
    exact hN'.2 x hx
  have hMe : IsEvenInt c 𝔬 h M := by
    unfold IsEvenInt
    refine ⟨?_, fun x hx => hx⟩
    rintro x ⟨a, ha, hx⟩ y ⟨b, hb, hy⟩
    exact key x y a b ha hb hx hy
  have heq : ∀ N : Submodule 𝔬 V, IsMaxEven c 𝔬 h N → N = M := by
    intro N hN'
    unfold IsMaxEven at hN'
    exact le_antisymm (hLM N hN'.2.1) (hN'.2.2 M hMe (hLM N hN'.2.1))
  refine ⟨LinearEquiv.refl R V, ?_⟩
  unfold IsIsomOnto
  refine ⟨fun x y => rfl, fun z => ?_⟩
  rw [heq L hL, heq L' hL']
  rfl

theorem hasBase_of_split {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k) (φ : R ≃+* k × k) (c : R →+* R)
    (𝔬 : Subring R) (hc : ∀ r, φ (c r) = (φ r).swap) (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) : HasBase c 𝔬 := by
  unfold HasBase
  intro V _ _ _ h hH hP hiso L L' hL hL'
  rcases _root_.GlobalTheory.CompanionTheory.KFin.hermSwap_struct φ c hc h hH hP hiso with hsub | ⟨w₀, hspan, hunit⟩
  · refine ⟨LinearEquiv.refl R V, ?_⟩
    unfold IsIsomOnto
    refine ⟨fun _ _ => rfl, fun z => ?_⟩
    rw [Subsingleton.elim z 0, LinearEquiv.refl_apply]
    exact ⟨fun _ => L'.zero_mem, fun _ => L.zero_mem⟩
  · let f : R →ₗ[𝔬] V :=
      { toFun := fun r => r • w₀
        map_add' := fun a b => add_smul a b w₀
        map_smul' := fun s r => by
          simp only [RingHom.id_apply, Subring.smul_def, smul_eq_mul, mul_smul] }
    have hf : ∀ r, f r = r • w₀ := fun r => rfl
    have finj : Function.Injective f := by
      intro a b hab
      rw [hf, hf] at hab
      have h1 := congrArg (h w₀) hab
      rw [hH.smul_right, hH.smul_right] at h1
      exact hunit.mul_left_injective h1
    have fsurj : Function.Surjective f := fun x => by
      obtain ⟨r, hr⟩ := hspan x
      exact ⟨r, by rw [hf, hr]⟩
    have desc : ∀ N : Submodule 𝔬 V, IsMaxEven c 𝔬 h N → ∃ α β : k,
        (α ≠ 0 ∧ β ≠ 0 ∧ ∃ u ∈ O, u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u) ∧
        ∀ r : R, r • w₀ ∈ N ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ ∃ y ∈ O, (φ r).2 = β * y := by
      intro N hN
      have hNfg : N.FG := by
        have h' := hN
        unfold IsMaxEven IsLat at h'
        exact h'.1.1
      have hfg : (N.comap f).FG := by
        apply Submodule.fg_of_fg_map_injective f finj
        rw [Submodule.map_comap_eq_of_surjective fsurj]
        exact hNfg
      obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.split_order_fg_ideal_product O φ 𝔬 h𝔬 (N.comap f) hfg
      have hαβ' : ∀ r : R, r • w₀ ∈ N ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ ∃ y ∈ O, (φ r).2 = β * y :=
        fun r => hαβ r
      exact ⟨α, β, _root_.GlobalTheory.CompanionTheory.KFin.RankOne.unimodular_coords O φ c 𝔬 hc h𝔬 h hH w₀ hspan hunit N hN α β hαβ', hαβ'⟩
    obtain ⟨α, β, ⟨hα, hβ, u, hu, hu', hud⟩, hL1⟩ := desc L hL
    obtain ⟨α', β', ⟨hα', hβ', u', hu2, hu2', hud'⟩, hL2⟩ := desc L' hL'
    have hd0 : (φ (h w₀ w₀)).1 ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := hunit.exists_right_inv
      have h2 := congrArg (fun x => (φ x).1) ht
      simp only [map_mul, Prod.fst_mul, map_one, Prod.fst_one, h0, zero_mul] at h2
      exact zero_ne_one h2
    have hs : α' / α * (α / α') = 1 := by field_simp
    let us : Rˣ :=
      { val := φ.symm (α' / α, α / α')
        inv := φ.symm (α / α', α' / α)
        val_inv := by
          apply φ.injective
          rw [map_mul, map_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Prod.mk_mul_mk, hs,
            mul_comm (α / α') (α' / α), hs] <;> rfl
        inv_val := by
          apply φ.injective
          rw [map_mul, map_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Prod.mk_mul_mk,
            mul_comm (α / α') (α' / α), hs] <;> rfl }
    let p : V ≃ₗ[R] V := LinearEquiv.smulOfUnit us
    have hp : ∀ x, p x = φ.symm (α' / α, α / α') • x := fun x => rfl
    refine ⟨p, ?_⟩
    unfold IsIsomOnto
    refine ⟨fun x y => ?_, fun z => ?_⟩
    · have hcs : c (φ.symm (α' / α, α / α')) * φ.symm (α' / α, α / α') = 1 := by
        apply φ.injective
        rw [map_mul, hc, RingEquiv.apply_symm_apply, map_one, Prod.swap_prod_mk, Prod.mk_mul_mk,
          mul_comm (α / α') (α' / α), hs] <;> rfl
      rw [hp, hp, herm_smul_left hH, hH.smul_right, ← mul_assoc, hcs, one_mul]
    · obtain ⟨r, rfl⟩ := hspan z
      rw [hp, smul_smul, hL1, hL2]
      have e1 : (φ (φ.symm (α' / α, α / α') * r)).1 = α' / α * (φ r).1 := by
        rw [map_mul, RingEquiv.apply_symm_apply]; rfl
      have e2 : (φ (φ.symm (α' / α, α / α') * r)).2 = α / α' * (φ r).2 := by
        rw [map_mul, RingEquiv.apply_symm_apply]; rfl
      rw [e1, e2]
      constructor
      · rintro ⟨⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩⟩
        refine ⟨⟨x, hx, ?_⟩, ⟨u * u'⁻¹ * y, mul_mem (mul_mem hu hu2') hy, ?_⟩⟩
        · rw [hx1]
          field_simp
        · rw [hy1, ← hud, ← hud']
          field_simp <;> ring
      · rintro ⟨⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩⟩
        refine ⟨⟨x, hx, ?_⟩, ⟨u' * u⁻¹ * y, mul_mem (mul_mem hu2 hu') hy, ?_⟩⟩
        · have h3 : (φ r).1 = α / α' * (α' / α * (φ r).1) := by field_simp
          rw [h3, hx1]
          field_simp
        · have h3 : (φ r).2 = α' / α * (α / α' * (φ r).2) := by field_simp
          rw [h3, hy1, ← hud, ← hud']
          field_simp <;> ring

theorem hasBase_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), HasBase (sigR (Fv F v) σ) (intLoc F E v) := by
  intro F E _ _ _ _ _ σ hcm v
  by_cases hF : IsField (Fv F v ⊗[F] E)
  · obtain ⟨W, hW, hWc⟩ := _root_.GlobalTheory.CompanionTheory.KFin.FieldVal.exists_valuation hcm v hF
    refine hasBase_of_field (k := Fv F v) (sigR (Fv F v) σ) (intLoc F E v) W
      (fun a ha => hF.mul_inv_cancel ha) ?_ (fun a ha => _root_.GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap hcm (Fv F v) a ha) ?_ ?_ hWc ?_ ?_
    · intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [sigR, GlobalTheory.AdelicU.cm_conj_conj hcm]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    · intro x
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    · intro a
      rw [hW]
      exact mem_intLoc_iff_absFin_le_one
    · intro a ha
      by_contra hne
      obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
      have h2 := congrArg W hb
      rw [map_mul, ha, zero_mul, map_one] at h2
      exact zero_ne_one h2
    · intro e he
      replace he : ‖e‖₊ < 1 := by
        rw [hW] at he
        simpa [Algebra.TensorProduct.algebraMap_apply, absFin_tmul_one] using he
      have he1 : e ∈ HeightOneSpectrum.adicCompletionIntegers F v := nnnorm_le_one_iff_mem.1 he.le
      have hv : Valued.v e < 1 := by
        have hle1 : Valued.v e ≤ 1 := he1
        rcases lt_or_eq_of_le hle1 with h1 | h1
        · exact h1
        · exfalso
          have he0 : e ≠ 0 := by
            intro h0
            rw [h0, map_zero] at h1
            exact zero_ne_one h1
          have hinvm : e⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
            show Valued.v e⁻¹ ≤ 1
            rw [map_inv₀, h1, inv_one]
          have hle := nnnorm_le_one_iff_mem.2 hinvm
          have h2 : ‖e * e⁻¹‖₊ = 1 := by rw [mul_inv_cancel₀ he0, nnnorm_one]
          rw [nnnorm_mul] at h2
          have h3 : ‖e‖₊ * ‖e⁻¹‖₊ < 1 := lt_of_le_of_lt (mul_le_of_le_one_right zero_le hle) he
          rw [h2] at h3
          exact lt_irrefl _ h3
      obtain ⟨a, ha⟩ := GlobalTheory.InertUnitNorm.exists_root_quadratic_of_approx v 1 ⟨e, he1⟩ 0
        (by simpa using hv) (by simp)
      refine ⟨(a : Fv F v), ?_⟩
      have h2 : (a : Fv F v) ^ 2 + 1 * (a : Fv F v) + e = 0 := by
        have h3 := congrArg Subtype.val ha
        simpa using h3
      linear_combination h2
  · obtain ⟨φ, hφc, hφ𝔬⟩ := _root_.GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv hcm v hF
    exact hasBase_of_split (HeightOneSpectrum.adicCompletionIntegers F v) φ _ _ hφc hφ𝔬

end GlobalTheory.CompanionTheory.KFin.Base
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicOfFlagPreserving
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

theorem mem_parRat_frameFlag_firstCols : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) (δ : GF V),
    (∀ l : Fin r, l ≤ j → ∃ b : Fin r → D.host.E, δ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) →
    δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm := by
  intro D V r X Y hW j δ h
  have hcoord : ∀ c : Fin V.rank → D.host.E, ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V c) =
      GlobalTheory.AutFunCompare.vecOf V (δ.1.1 *ᵥ c) := by
    intro c
    refine V.frame.ext_elem fun i => ?_
    rw [GlobalTheory.AutFunCompare.repr_vecOf, ratAct, Matrix.repr_toLin]
    congr 1
    funext a
    exact GlobalTheory.AutFunCompare.repr_vecOf V c a
  have hspan : ∀ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j),
      ratAct D.sp.cm V δ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j) := by
    have hle : GlobalTheory.AutFunCompare.colSpan V (firstCols X j) ≤
        (GlobalTheory.AutFunCompare.colSpan V (firstCols X j)).comap (ratAct D.sp.cm V δ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      obtain ⟨b, hb, hb0⟩ := h (Fin.castLE j.2 k) (Nat.lt_succ_iff.1 k.2)
      have hcol : (firstCols X j)ᵀ k = fun a => X a (Fin.castLE j.2 k) := rfl
      change ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V ((firstCols X j)ᵀ k)) ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j)
      rw [hcoord, hcol, hb]
      have hsum : X *ᵥ b = ∑ l, b l • (fun a => X a l) := by
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, GlobalTheory.AutFunCompare.vecOf, map_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [map_smul]
      by_cases hl : l ≤ j
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l.val, Nat.lt_succ_iff.2 hl⟩, rfl⟩)
      · rw [hb0 l (not_le.1 hl), zero_smul]
        exact Submodule.zero_mem _
    exact fun x hx => hle hx
  change GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH D.sp.cm.sig V.gram D.host.F δ ∈ IsoFlag.par _ D.sp.cm D.host.F
  rw [frameFlag, IsoFlag.par_single, diagH_mem_parab]
  exact hspan

end GlobalTheory.CompanionTheory.RegInt
end
end

