module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fv_exists_skew (hσ : IsCMExt F E σ) : ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  obtain ⟨-, hE, -, hc⟩ := hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hss : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hc, hc, star_star])
  by_contra hn
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have hx : x - σ x = 0 := by
    by_contra h
    exact hn ⟨_, h, by rw [map_sub, hss, neg_sub]⟩
  have h2 := hc τ x
  rw [← sub_eq_zero.1 hx] at h2
  exact h2.symm

theorem fv_exists_herm (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : EpsHerm σ J) :
    ∃ c : E, c ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (c • J)ᵀ := by
  have hd : ∀ c : E, c ≠ 0 → ((c • J)ᵀ).det ≠ 0 := fun c hc => by
    rw [Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hJ.2
  rcases hJ.1 with h | h
  · exact ⟨1, one_ne_zero, fun i j => by simpa using h j i, hd 1 one_ne_zero⟩
  · obtain ⟨c, hc, hs⟩ := fv_exists_skew hσ
    refine ⟨c, hc, fun i j => ?_, hd c hc⟩
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs, h j i]
    ring

omit [NumberField E] in
theorem fv_HR_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    UG (cA σ) (incM F J) = HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (c • J)ᵀ := by
  have hu : IsUnit (inclR (F := F) (AF F) c) := (IsUnit.mk0 c hc).map _
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ = (inclR (F := F) (AF F) c • incM F J)ᵀ := by
    ext i j
    exact map_mul (inclR (F := F) (AF F)) c (J j i)
  ext g
  show g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J ↔
    (g.1.map (cA σ))ᵀ * HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ * g.1 = HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ
  rw [hJ]
  have e : (g.1.map (cA σ))ᵀ * (inclR (F := F) (AF F) c • incM F J)ᵀ * g.1 =
      (inclR (F := F) (AF F) c • (g.1ᵀ * incM F J * g.1.map (cA σ)))ᵀ := by
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc]
  rw [e, Matrix.transpose_inj, hu.smul_left_cancel]

omit [NumberField E] in
theorem fv_rat_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))).range.subgroupOf (HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ J) =
      HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
  ext g
  rw [HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have h : ((γ.1.map (inclR (F := F) (AF F))).map (sigR (AF F) σ))ᵀ * J.map (inclR (F := F) (AF F)) *
        γ.1.map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F)) := by
      have h0 := g.2
      rw [← hγ] at h0
      exact h0
    show (γ.1.map (σ : E →+* E))ᵀ * J * γ.1 = J
    refine Matrix.map_injective hinj ?_
    show ((γ.1.map (σ : E →+* E))ᵀ * J * γ.1).map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F))
    rw [Matrix.map_mul, Matrix.map_mul]
    exact h
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩

theorem fundamental_domain_finite_volume (hσ : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (S : Subgroup (GL (Fin n) (AE F E))) (hS : S = HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ J) :
    letI : MeasurableSpace S := borel S
    ∀ (μ : Measure S) (D : Set S), μ.IsHaarMeasure →
      IsFundamentalDomain ((Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))).range.subgroupOf S) D μ →
        μ D < ⊤ := by
  subst hS
  rw [fv_rat_eq]
  intro μ D hμ hD
  exact ((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hσ n J hJ).2 μ hμ).2 D hD

theorem finVolU : FinVolU := by
  intro F E _ _ _ _ _ σ hσ n J hJ
  obtain ⟨c, hc, h⟩ := fv_exists_herm hσ hJ
  exact fundamental_domain_finite_volume hσ _ h _ (fv_HR_eq J hc)

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem countable_numberField' (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Countable (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  have := countable_numberField' K
  have : Countable (NumberField.RingOfIntegers K) :=
    Function.Injective.countable (NumberField.RingOfIntegers.coe_injective (K := K))
  have hI : Countable (Ideal (NumberField.RingOfIntegers K)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (NumberField.RingOfIntegers K) => Ideal.span (s : Set (NumberField.RingOfIntegers K))) ?_
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  exact Function.Injective.countable
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) => v.asIdeal)
    (fun v w h => IsDedekindDomain.HeightOneSpectrum.ext h)

private theorem univ_le_preimage_inf_of_univ_le (K : Type) [Field K] [NumberField K] :
    T2Space (NumberField.InfiniteAdeleRing K) ∧ SecondCountableTopology (NumberField.InfiniteAdeleRing K) := by
  have h : ∀ v : NumberField.InfinitePlace K, SecondCountableTopology v.Completion := fun v =>
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact ⟨inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion)),
    inferInstanceAs (SecondCountableTopology ((v : NumberField.InfinitePlace K) → v.Completion))⟩

private theorem fin_lemma_4 (K : Type) [Field K] [NumberField K] :
    T2Space (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) ∧
      SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) := by
  have := countable_numberField' K
  have := countable_heightOneSpectrum_ringOfIntegers K
  have hsep : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      SecondCountableTopology (v.adicCompletion K) := by
    intro v
    have : TopologicalSpace.SeparableSpace (v.adicCompletion K) :=
      ⟨⟨_, Set.countable_range _, IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v⟩⟩
    exact UniformSpace.secondCountable_of_separable _
  have hopen : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    Valued.isOpen_valuationSubring _
  unfold IsDedekindDomain.FiniteAdeleRing
  constructor
  · exact T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  · have hS : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Filter.cofinite : Filter (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) ≤
          Filter.principal ((s : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ) :=
      fun s => Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have hemb : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        Topology.IsOpenEmbedding (RestrictedProduct.inclusion (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (hS s)) := fun s =>
      RestrictedProduct.isOpenEmbedding_inclusion_principal hopen (hS s)
    have hsc : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        SecondCountableTopology (Set.range (RestrictedProduct.inclusion (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (hS s))) := by
      intro s
      have : SecondCountableTopology (RestrictedProduct (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
          (Filter.principal ((s : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ))) :=
        RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
      exact (hemb s).isEmbedding.toHomeomorph.symm.secondCountableTopology
    refine @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ _ hsc (fun s => (hemb s).isOpen_range) ?_
    refine Set.eq_univ_of_forall fun x => ?_
    have hx := Filter.eventually_cofinite.mp x.2
    refine Set.mem_iUnion.mpr ⟨hx.toFinset, ⟨x.1, ?_⟩, rfl⟩
    exact Filter.eventually_principal.mpr fun v hv => by simpa using hv

private theorem AF_t2_secondCountable (K : Type) [Field K] [NumberField K] :
    T2Space (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) ∧ SecondCountableTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) := by
  obtain ⟨h1, h2⟩ := univ_le_preimage_inf_of_univ_le K
  obtain ⟨h3, h4⟩ := fin_lemma_4 K
  exact ⟨inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K)),
    inferInstanceAs (SecondCountableTopology (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))⟩

private theorem AE_t2_secondCountable_locallyCompact (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    T2Space (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) ∧ SecondCountableTopology (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) ∧
      LocallyCompactSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) := by
  obtain ⟨h1, h2⟩ := AF_t2_secondCountable K
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := K) (E := L)
  have : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) := inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))
  have : ContinuousAdd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) :=
    IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L))
  let b := Module.finBasis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L))
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc' : Continuous b.equivFun.symm := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L) ≃ₜ (Fin _ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) :=
    { toEquiv := b.equivFun.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  exact ⟨h.isEmbedding.t2Space, h.isEmbedding.secondCountableTopology, h.isClosedEmbedding.locallyCompactSpace⟩

private theorem GL_t2_secondCountable_locallyCompact (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] [LocallyCompactSpace R] (n : ℕ) :
    T2Space (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ LocallyCompactSpace (GL (Fin n) R) := by
  have : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  let ι : GL (Fin n) R → Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R := fun g => (↑g, ↑g⁻¹)
  have he : Topology.IsEmbedding ι := by
    exact ((Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp Units.isEmbedding_embedProduct
  have hr : Set.range ι = {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.mul_inv, g.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨p.1, p.2, h1, h2⟩, rfl⟩
  have hcl : IsClosed (Set.range ι) := by
    rw [hr]
    exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  have hce : Topology.IsClosedEmbedding ι := ⟨he, hcl⟩
  exact ⟨he.t2Space, he.secondCountableTopology, hce.locallyCompactSpace⟩

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  obtain ⟨h1, h2⟩ := AF_t2_secondCountable F
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := F) (E := E)
  have : IsTopologicalRing (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
  obtain ⟨a1, a2, a3⟩ := AE_t2_secondCountable_locallyCompact F E
  obtain ⟨g1, g2, g3⟩ := GL_t2_secondCountable_locallyCompact (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) n
  have : T2Space (Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (T2Space (Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    IsModuleTopology.continuous_of_linearMap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ).toLinearMap
  have hcl : IsClosed (GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) :
      Set (GL (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  have hlc := hcl.locallyCompactSpace
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA
  exact ⟨hlc, Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩

theorem continuous_ht (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (ht : UA σ J → ℝ≥0) := by
  exact (GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val

theorem grpTop_of : GrpTop := by
  unfold GrpTop
  intro F E _ _ _ _ _ σ _ n J _
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hM : Countable (Matrix (Fin n) (Fin n) E) := by
    unfold Matrix
    infer_instance
  have hG : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) (fun a b hab => Units.ext hab)
  let f := Matrix.GeneralLinearGroup.map (n := Fin n)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F))
  have hR : Countable (Set.range f) := (Set.countable_range f).to_subtype
  refine ⟨(lcsc_UA σ J).1, (lcsc_UA σ J).2.1, (lcsc_UA σ J).2.2, ?_,
    GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J,
    Units.continuous_val.comp continuous_subtype_val, ?_, ?_⟩
  · have key : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J,
        ((x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) : GL (Fin n) _) ∈ Set.range f :=
      fun x => MonoidHom.mem_range.mp x.2
    refine Function.Injective.countable
      (f := fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J => (⟨_, key x⟩ : Set.range f)) ?_
    intro x y h
    have h0 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h0)
  · intro g h
    rfl
  · intro Ω hΩ
    obtain ⟨C, hC⟩ := (hΩ.image (continuous_ht σ J)).bddAbove
    exact ⟨C, fun g hg => hC ⟨g, hg, rfl⟩⟩

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.IsCompactIntV
section
noncomputable section

namespace PositivityTheory.ThKEst.FiniteAdelicSupportCompactness

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def stdF (κ : Type) (u : HeightOneSpectrum (𝓞 F)) : (κ → Fv F u) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1

def Good (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) : Prop :=
  (∀ u, φ u ∈ SB (κ → Fv F u)) ∧ ∀ᶠ u in cofinite, φ u = stdF κ u

def pf (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) (y : κ → Af F) : ℂ :=
  ∏ᶠ u, φ u fun i => evalV F u (y i)

theorem pure_eq (f : SInf F κ) (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) :
    pure f φ = pureA F f (pf φ) := rfl

theorem ev_int (y : κ → Af F) : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  eventually_all.2 fun i => (y i).2

theorem cont_evalV (u : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F u) :=
  (continuous_apply u).comp RestrictedProduct.continuous_coe

theorem isOpen_intAf : IsOpen {a : Af F | ∀ v, evalV F v a ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intV (u : HeightOneSpectrum (𝓞 F)) :
    IsCompact {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  have h : IsCompact (u.adicCompletionIntegers F : Set (Fv F u)) := isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F u)
  simpa [Set.pi] using isCompact_univ_pi fun _ : κ => h

theorem isCompact_box (C : ∀ u : HeightOneSpectrum (𝓞 F), Set (Fv F u)) (hC : ∀ u, IsCompact (C u))
    (h : ∀ᶠ u in cofinite, C u ⊆ u.adicCompletionIntegers F) : IsCompact {a : Af F | ∀ u, evalV F u a ∈ C u} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {u | C u ⊆ u.adicCompletionIntegers F}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 h
  let P := RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 S)
  have h1 : IsCompact {x : P | ∀ u, x u ∈ C u} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hC
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ u -
      exact hy u
    · intro hx
      exact ⟨⟨x, fun u hu => hu (hx u trivial)⟩, fun u => hx u trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : Af F | ∀ u, evalV F u a ∈ C u} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ u, x u ∈ C u} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨a.1, fun u hu => hu (ha u)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

theorem pf_eq_prod {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : κ → Af F) (h : ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F) :
    pf φ y = ∏ u ∈ S, φ u fun i => evalV F u (y i) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
  by_contra hn
  apply hu
  simp only
  rw [(h u hn).1, stdF, Set.indicator_of_mem (by exact (h u hn).2)]
  rfl

theorem exists_fin {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u)
    (y : κ → Af F) : ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  ⟨(hφ.and (ev_int y)).toFinset, fun u hu => by
    by_contra hn
    exact hu (Set.Finite.mem_toFinset _ |>.2 hn)⟩

theorem pf_mem {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) : pf φ ∈ SB (κ → Af F) := by
  have hc : ∀ u, Continuous fun (y : κ → Af F) i => evalV F u (y i) := fun u =>
    continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨S, hS⟩ := exists_fin hφ.2 x
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i v, evalV F v (y i - x i) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => (isOpen_intAf.preimage (f := fun y : κ → Af F => y i - x i) (by fun_prop)).mem_nhds
        (by intro v; simp)
    have h2 : ∀ᶠ y in 𝓝 x, ∀ u ∈ S, φ u (fun i => evalV F u (y i)) = φ u fun i => evalV F u (x i) :=
      (eventually_all_finset S).2 fun u _ => ((hφ.1 u).1.comp_continuous (hc u)).eventually_eq x
    filter_upwards [h1, h2] with y h1 h2
    rw [pf_eq_prod S x hS, pf_eq_prod S y fun u hu => ⟨(hS u hu).1, fun i => ?_⟩]
    · exact Finset.prod_congr rfl h2
    · have := add_mem (h1 i u) ((hS u hu).2 i)
      rwa [map_sub, sub_add_cancel] at this
  · have hK : ∀ i : κ, IsCompact {a : Af F | ∀ u, evalV F u a ∈ (fun x => x i) '' tsupport (φ u)} := fun i =>
      isCompact_box _ (fun u => (hφ.1 u).2.isCompact.image (continuous_apply i)) (by
        filter_upwards [hφ.2] with u hu
        rintro _ ⟨x, hx, rfl⟩
        rw [hu] at hx
        exact closure_minimal Set.support_indicator_subset (isCompact_intV u).isClosed hx i)
    refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
    by_contra h0
    refine hy fun i _ u => ⟨fun i => evalV F u (y i), subset_tsupport _ (fun h => h0 ?_), rfl⟩
    obtain ⟨S, hS⟩ := exists_fin hφ.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h)]
    exact Finset.prod_eq_zero (Finset.mem_insert_self _ _) h

theorem smul_pureA (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) : c • pureA F f g = pureA F (c • f : SInf F κ) g := by
  funext x
  simp [pureA, mul_assoc]

theorem sum_of_span {S : Set ((κ → AF F) → ℂ)} {T : Set ((κ → Af F) → ℂ)}
    (h : ∀ Φ ∈ S, ∃ (f : SInf F κ) (g : (κ → Af F) → ℂ), g ∈ T ∧ Φ = pureA F f g) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ Submodule.span ℂ S) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (φ : Fin m → (κ → Af F) → ℂ), (∀ i, φ i ∈ T) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f φ h1 h2 using fun i => h (g i) (g i).2
  refine ⟨m, fun i => c i • f i, φ, h1, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h2, smul_pureA]

theorem exists_one : ∃ f : SInf F κ, f 0 = 1 := by
  classical
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  exact ⟨hs.toSchwartzMap hc, by simp [h2]⟩

def finPt (y : κ → Af F) : κ → AF F := fun i => ((0, y i) : AF F)

theorem pureA_zero (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (y : κ → Af F) :
    pureA F f g (finPt y) = f 0 * g y := by
  have e : (fun _ : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) = 0 := funext fun _ => map_zero _
  exact congrArg (fun z => f z * g y) e

end PositivityTheory.ThKEst.FiniteAdelicSupportCompactness

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK FiniteAdelicSupportCompactness

theorem soFin_of : SoFin := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have good : ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      pf φ ∈ SB (Fin n × Fin d → Af F) := fun φ h1 h2 =>
    pf_mem ⟨h1, by
      filter_upwards [h2, hP.good.std] with v a b
      exact a.trans b⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun φ hφ => ?_⟩
  · refine sum_of_span (T := soFin B M) ?_ hΦ
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, pf φ, ⟨good φ h1 h2, fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩⟩, rfl⟩
  · refine sum_of_span (T := (SB (Fin n × Fin d → Af F) : Set _)) ?_ hΦ
    rintro _ ⟨f, g, h1, rfl⟩
    exact ⟨f, g, h1, rfl⟩
  · refine (Submodule.span_le.2 ?_ : M.So B.ψ B.τ₁ ≤ schA F _) hΦ
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    exact Submodule.subset_span ⟨f, pf φ, good φ h1 h2, rfl⟩
  · obtain ⟨f₀, h0⟩ := exists_one (F := F) (κ := Fin n × Fin d)
    obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 (hφ.2 f₀)
    choose f χ h1 h2 h3 h4 using fun i => (g i).2
    have e : ∀ y, φ y = ∑ i, c i * f i 0 * pf (χ i) y := fun y => by
      have := congrFun hg (finPt y)
      rw [pureA_zero, h0, one_mul, Finset.sum_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h4, pure_eq, Pi.smul_apply, pureA_zero, smul_eq_mul, mul_assoc]
    refine ⟨m, fun i => c i * f i 0, χ, fun i => ⟨h1 i, h2 i, h3 i⟩, fun f' => ?_⟩
    funext x
    rw [Finset.sum_apply]
    simp only [pure_eq, pureA, Pi.smul_apply, smul_eq_mul, e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end PositivityTheory.ThKEst

end
end

