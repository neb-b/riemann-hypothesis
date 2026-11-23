module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalMeasuresOrthogonalSumAlmostAllPlaces
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneProduct

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleTop

theorem t2Space_finiteAdeleRing_of_numberField (F : Type) [Field F] [NumberField F] : T2Space (Af F) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

theorem t2Space_infiniteAdeleRing_of_numberField_field (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

theorem adele_top : ∀ (F : Type) [Field F] [NumberField F],
    (LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)) ∧
    (LocallyCompactSpace (Af F) ∧ SecondCountableTopology (Af F) ∧ T2Space (Af F)) := by
  intro F _ _
  refine ⟨⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_adele F, ?_⟩,
    GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, t2Space_finiteAdeleRing_of_numberField F⟩
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.CompanionTheory.AdeleTop
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerBox

section Box

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem pureL_indicator_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf (fun v => (A v).indicator 1) X =
      {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}.indicator
        (fun X => φinf (projInf X)) X := by
  by_cases hX : ∀ v, projV v (projFin X) ∈ A v
  · have hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun v hv => by
      rw [← hS v hv]; exact hX v
    have hB : X ∈ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [pureL, Set.indicator_of_mem hI, Set.indicator_of_mem hB,
      Finset.prod_eq_one (fun v _ => Set.indicator_of_mem (hX v) _), mul_one]
  · have hB : X ∉ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [Set.indicator_of_notMem hB]
    obtain ⟨v, hv⟩ := not_forall.1 hX
    by_cases hvS : v ∈ S
    · by_cases hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))
      · rw [pureL, Set.indicator_of_mem hI,
          Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _), mul_zero]
      · rw [pureL, Set.indicator_of_notMem hI]
    · have hI : X ∉ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun h => hv (by
        rw [hS v hvS]; exact h v hvS)
      rw [pureL, Set.indicator_of_notMem hI]

theorem box_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) :
    {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
      intOff b S ∩ ⋂ v ∈ S, (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) ⁻¹' A v := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨fun v hv => by rw [← hS v hv]; exact h v, fun v _ => h v⟩
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · exact h2 v hv
    · rw [hS v hv]; exact h1 v hv

end Box

theorem measurableSet_box (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  have : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := hB n M
  obtain ⟨-, hFin, hV, -, hOff, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  have hmeas : ∀ v, Measurable
      (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) := fun v => by
    have hc : Continuous (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) :=
      (hV v).comp hFin
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
    have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
    exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable
  rw [box_eq b S A hS]
  exact (hOff S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => hmeas v (hA v))

theorem euler_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I c minf m → ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable φinf → (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) < ⊤) → (∀ᶠ v in Filter.cofinite, A v = latV b v) → Multipliable (fun v => (m v (A v)).toReal) ∧ ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I = (c : ℝ≥0∞) * (∫⁻ X, φinf X ∂minf) * ENNReal.ofReal (∏' v, (m v (A v)).toReal) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m hE φinf A hφ hA hfin hcof
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  have hfinite : {v | ¬ A v = latV b v}.Finite := Filter.eventually_cofinite.1 hcof
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ hfinite.toFinset with hSdef
  have hS : ∀ v, v ∉ S → A v = latV b v := fun v hv => by
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfinite.mem_toFinset.2 hne))
  have hsumA : Summable (fun v => |(m v (A v)).toReal - 1|) :=
    hsum.congr_cofinite (hcof.mono fun v hv => by simp only [hv])
  obtain ⟨hmul, hsplit, -, hnn⟩ := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ _ hsumA
  refine ⟨hmul, ?_⟩
  have hbox := measurableSet_box F E σ hσ b n M S A hA hS
  have hform := hS₀ S Finset.subset_union_left φinf (fun v => (A v).indicator 1) hφ
    (fun v => measurable_one.indicator (hA v))
  have hlhs : ∫⁻ X, pureL b S φinf (fun v => (A v).indicator 1) X ∂I =
      ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I := by
    simp_rw [pureL_indicator_eq b S φinf A hS]
    exact lintegral_indicator hbox _
  have hloc : ∀ v, ∫⁻ X, (A v).indicator 1 X ∂(m v) = ENNReal.ofReal (m v (A v)).toReal := fun v => by
    rw [lintegral_indicator_one (hA v), ENNReal.ofReal_toReal (hfin v).ne]
  have htail : ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal =
      ∏' v : {v // v ∉ S}, (m v.1 (A v.1)).toReal :=
    tprod_congr fun v => by rw [hS v.1 v.2]
  rw [hlhs] at hform
  rw [hform, htail, (hsplit S).2]
  simp_rw [hloc]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun v _ => ENNReal.toReal_nonneg]
  ring

end GlobalTheory.CompanionTheory.SW.EulerBox
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasures
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StdEx

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open NumberField.mixedEmbedding
open scoped TensorProduct ENNReal NNReal Matrix

variable (F : Type) [Field F] [NumberField F]

theorem exists_isStdV (v : HeightOneSpectrum (𝓞 F)) : ∃ lam : Measure (Fv F v), IsStdV v lam := by
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hc := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let K : TopologicalSpace.PositiveCompacts (Fv F v) :=
    ⟨⟨(v.adicCompletionIntegers F : Set (Fv F v)), isCompact_iff_compactSpace.2 hc⟩, by
      change (interior (v.adicCompletionIntegers F : Set (Fv F v))).Nonempty
      have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
        Valued.isOpen_valuationSubring _
      rw [hO.interior_eq]
      exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩


omit [NumberField F] in
theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)


omit [NumberField F] in
theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem mem_span_iff (x : mixedSpace F) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis F)) ↔
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x ∈
        ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range := by
  have hk : x ∈ mixedEmbedding.integerLattice F ↔ ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
    simp [LinearMap.mem_range]
  rw [mem_span_latticeBasis, hk]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact ha

theorem exists_isStdInf : ∃ laminf : Measure (Ainf F), IsStdInf laminf := by
  classical
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hce : Continuous e := continuous_toMixed F
  have hcs : Continuous e.symm := continuous_ofMixed F
  let D₀ : Set (mixedSpace F) := ZSpan.fundamentalDomain (latticeBasis F)
  let μ₀ : Measure (mixedSpace F) := volume
  have h0 : μ₀ D₀ ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero (latticeBasis F)
  have ht : μ₀ D₀ ≠ ∞ := (ZSpan.fundamentalDomain_isBounded (latticeBasis F)).measure_lt_top.ne
  have hD₀ : MeasurableSet D₀ := ZSpan.fundamentalDomain_measurableSet (latticeBasis F)
  let c : ℝ≥0 := ((μ₀ D₀).toNNReal)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (ENNReal.toNNReal_ne_zero.2 ⟨h0, ht⟩)
  let μ₁ : Measure (mixedSpace F) := c • μ₀
  have : μ₁.IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ₀ hc
  have hμ₁ : μ₁ D₀ = 1 := by
    have hv : ((μ₀ D₀).toNNReal : ℝ≥0∞) = μ₀ D₀ := ENNReal.coe_toNNReal ht
    have hne : (μ₀ D₀).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.2 ⟨h0, ht⟩
    change (c • μ₀) D₀ = 1
    rw [Measure.smul_apply, ← hv, ENNReal.smul_def, smul_eq_mul, hv, ← hv, ← ENNReal.coe_mul,
      inv_mul_cancel₀ hne, ENNReal.coe_one]
  let E : Ainf F ≃ᵐ mixedSpace F :=
    (Homeomorph.mk e.toEquiv hce hcs).toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  let lam : Measure (Ainf F) := Measure.map e.symm μ₁
  have hlamE : lam = Measure.map E.symm μ₁ := rfl
  have hmp : MeasurePreserving E lam μ₁ := by
    refine ⟨E.measurable, ?_⟩
    rw [hlamE, Measure.map_map E.measurable E.symm.measurable]
    simp
  refine ⟨lam, ?_, e ⁻¹' D₀, ?_, ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map μ₁ e.symm.toAddEquiv hcs hce
  · have hF₀ := ZSpan.isAddFundamentalDomain (latticeBasis F) μ₁
    refine hF₀.preimage_of_equiv (f := e) hmp.quasiMeasurePreserving
      (e := fun g => ⟨e.symm g.1, (mem_span_iff F g.1).1 g.2⟩) ⟨?_, ?_⟩ ?_
    · intro g h hgh
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val hgh))
    · rintro ⟨y, hy⟩
      refine ⟨⟨e y, (mem_span_iff F (e y)).2 (by
        change e.symm (e y) ∈ _
        rw [e.symm_apply_apply]
        exact hy)⟩, ?_⟩
      exact Subtype.ext (e.symm_apply_apply y)
    · intro g x
      change e (e.symm g.1 + x) = g.1 + e x
      rw [map_add (f := _), e.apply_symm_apply]
  · exact (hmp.measure_preimage hD₀.nullMeasurableSet).trans hμ₁

theorem exists_std : ∀ (F : Type) [Field F] [NumberField F],
    (∃ laminf : Measure (Ainf F), IsStdInf laminf) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∃ lam : Measure (Fv F v), IsStdV v lam :=
  fun F _ _ => ⟨exists_isStdInf F, exists_isStdV F⟩

end GlobalTheory.CompanionTheory.SW.StdEx
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneEventually
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodMass

theorem continuous_act_consTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (hring : IsTopologicalRing (R ⊗[F] E)) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA R σ J) :
    Continuous fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J h (consTup X) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actW, actTup, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  refine Fin.cases ?_ (fun a' => ?_) a
  · refine Fin.cases ?_ (fun j' => ?_) j <;> simpa [consTup] using continuous_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [consTup] using continuous_const
    · have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E => X a' j' :=
        (continuous_apply j').comp (continuous_apply a')
      simpa [consTup] using hc

theorem good_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdetT hT' d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [StageGood.stage_good F E σ hCM M J hJ t ht n T hT hdetT d b] with v hv
  intro lam hlam m m₁ m' hm hm₁ hm' c hc
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hH := coord_measures_haar F E σ hCM (Fv F v) d b lam hlam
  obtain ⟨hring, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E)) := by
    intro n' M'
    haveI := hB n' M'
    exact ((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := _root_.GlobalTheory.CompanionTheory.SW.fibre_block_stages F E σ hCM M J hJ t ht n T hT hdetT hT' (Fv F v) hLoc d b lam hlam
    m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))
  set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) =
        gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y :=
      (StageGood.gram_first (Fv F v) σ J t).trans hy1.symm
    obtain ⟨h, rfl⟩ := _root_.GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg
      (by rw [hg]; exact hy2)
    rw [hΨ h]
    haveI := hB n M
    haveI := hB (n + 1) (M + 1)
    have hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E |
        actW (Fv F v) σ _ h (consTup X) ∈ latV b v} :=
      (continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)
    have hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
        (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) =
        {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1 := by
      funext X
      rfl
    rw [hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]
  rw [← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae,
    lintegral_indicator_const (hlat _ _)]

end GlobalTheory.CompanionTheory.SW.GoodMass
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolume
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW

theorem latV_compact_open_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV (M := M) (n := n) b v) ∧ IsOpen (latV (M := M) (n := n) b v) ∧ (0 : Fin n → Fin M → Fv F v ⊗[F] E) ∈ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → coordW (Fv F v) b lam n M (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hσ d b n M v
  obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  let f : Fv F v ⊗[F] E → Fin d → Fv F v :=
    fun y k => (Algebra.TensorProduct.basis (Fv F v) b).repr y k
  let e : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v) := (hH d b).homeomorph f
  have hef : ∀ y, e y = f y := fun _ => rfl
  let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hOo : IsOpen O := Valued.isOpen_valuationSubring _
  have hOc : IsCompact O :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let P : Set (Fin d → Fv F v) := Set.pi Set.univ fun _ => O
  let B : Set (Fv F v ⊗[F] E) := e ⁻¹' P
  have hBc : IsCompact B :=
    (Homeomorph.isCompact_preimage e).2 (isCompact_univ_pi fun _ => hOc)
  have hBo : IsOpen B :=
    (Homeomorph.isOpen_preimage e).2 (isOpen_set_pi Set.finite_univ fun _ _ => hOo)
  have hlat : latV (M := M) (n := n) b v = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => B := by
    ext Y
    simp only [latV, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, B, P, Set.mem_preimage]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlat]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hBc
  · rw [hlat]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hBo
  · intro a i k
    simp
  · rintro lam ⟨hHaar, h1⟩
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : SecondCountableTopology (Fin d → Fv F v) := inferInstance
    have hme : MeasurableEmbedding f := e.measurableEmbedding
    have hsurj : Function.Surjective f := e.surjective
    haveI : SigmaFinite (coordK (Fv F v) b lam) := by
      refine SigmaFinite.of_map _ hme.measurable.aemeasurable (f := f) ?_
      change SigmaFinite (Measure.map f (Measure.comap f _))
      rw [hme.map_comap, hsurj.range_eq, Measure.restrict_univ]
      infer_instance
    have hK : coordK (Fv F v) b lam B = 1 := by
      change Measure.comap f _ B = 1
      rw [hme.comap_apply]
      have : f '' B = P := Set.image_preimage_eq _ hsurj
      rw [this, Measure.pi_pi]
      simp only [Finset.prod_const]
      change lam (v.adicCompletionIntegers F : Set (Fv F v)) ^ _ = 1
      rw [h1, one_pow]
    rw [hlat]
    unfold coordW
    rw [Measure.pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => hK

end GlobalTheory.CompanionTheory.SW
end
end

