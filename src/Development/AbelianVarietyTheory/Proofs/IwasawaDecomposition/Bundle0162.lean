module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
section
noncomputable section

namespace GlobalTheory.Mem.UnitaryEmb

open scoped TensorProduct
open NumberField Matrix

section General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (B A : HSpace E) (ι : B.V →ₗ[E] A.V) (h : HSpace.IsIsomEmb B A ι)

theorem continuous_embA : Continuous (embA hc B A ι h) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const))

theorem embA_ratA (γ : GRat hc B) : embA hc B A ι h (ratA hc B γ) = ratA hc A (embRat hc B A ι h γ) := by
  refine Subtype.ext (Units.ext ?_)
  show 1 + (embMat B A ι).map (inclR (F := F) (AF F)) *
      (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E).map (inclR (F := F) (AF F)) - 1) *
        (projMat hc B A ι).map (inclR (F := F) (AF F)) =
    (1 + embMat B A ι * (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E) - 1) *
      projMat hc B A ι).map (inclR (F := F) (AF F))
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_embHom (D : D7) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι) :
    ∃ s : GA D B →* GA D A, Continuous s ∧ (∀ h g, EmbRel A B ι g h ↔ g = s h) ∧ ∀ γ ∈ GQ B, s γ ∈ GQ A := by
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι, continuous_embA D.sp.cm B A ι hι,
    fun h g => GlobalTheory.AutFunCompare.embRel_iff A B ι hι g h, ?_⟩
  rw [GlobalTheory.AutFunCompare.GQ_eq, GlobalTheory.AutFunCompare.GQ_eq]
  rintro _ ⟨γ, rfl⟩
  exact ⟨_, (embA_ratA D.sp.cm B A ι hι γ).symm⟩

end GlobalTheory.Mem.UnitaryEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem exists_normalisation_of_locallyClosed : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (P U : Scheme.{0}) (s : P ⟶ Sp O) (Ω : P.Opens) (j : U ⟶ Ω.toScheme), IsProjOver s → IsClosedImmersion j → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U → Flat (j ≫ Ω.ι ≫ s) → ∃ (Z' : Scheme.{0}) (ν : Z' ⟶ P) (e : U ⟶ Z'), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧ IsPullback e j ν Ω.ι ∧ Dense (Set.range e) := by
  intro O _ _ _ P U s Ω j hs _ hn hfl
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs).1
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (j ≫ Ω.ι)
  obtain ⟨h, eh⟩ : ∃ h : U ⟶ P, h = j ≫ Ω.ι := ⟨_, rfl⟩
  have : QuasiCompact h := eh ▸ inferInstance
  have : IsSeparated h := eh ▸ inferInstance
  have : LocallyOfFiniteType h := eh ▸ inferInstance
  have : Flat (h ≫ s) := by rw [eh, Category.assoc]; exact hfl
  have : IsFinite h.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of O) h s
      fun x hx => charZero_residueField_of_flat (h ≫ s) hx
  have : Flat (h.toNormalization ≫ h.fromNormalization ≫ s) := by
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc]
    infer_instance
  exact ⟨h.normalization, h.fromNormalization, h.toNormalization, inferInstance,
    IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs, flat_normalization h _,
    isPullback_toNormalization_of_mono j Ω.ι h eh, h.toNormalization.denseRange⟩

end GlobalTheory.GraphClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FundDomDiscrete


open Topology Filter in
theorem exists_measurable_section {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ F : Set G, MeasurableSet F ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ F := by
  classical
  obtain ⟨W, hWo, hW⟩ : ∃ W : Set G, IsOpen W ∧ ((↑) : Γ → G) ⁻¹' W = {1} :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1W : (1 : G) ∈ W := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := by rw [hW]; rfl
    simpa using this
  obtain ⟨V0, hV0, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1W)
  obtain ⟨V, hVV0, hVo, h1V⟩ := mem_nhds_iff.1 hV0
  let U : G → Set G := fun g => {x | x * g⁻¹ ∈ V}
  have hUo : ∀ g, IsOpen (U g) := fun g => hVo.preimage (by fun_prop)
  have hUinj : ∀ g (γ : Γ) (x : G), x ∈ U g → (γ : G) * x ∈ U g → γ = 1 := by
    intro g γ x hx hγ
    have h := hVW _ (hVV0 hγ) _ (hVV0 hx)
    have h2 : (γ : G) * x * g⁻¹ / (x * g⁻¹) = γ := by
      rw [div_eq_mul_inv]; group
    rw [h2] at h
    have : γ ∈ ((↑) : Γ → G) ⁻¹' W := h
    rw [hW] at this
    exact this
  obtain ⟨s, hsc, hs⟩ := TopologicalSpace.countable_cover_nhds (f := U)
    (fun g => (hUo g).mem_nhds (by simpa [U] using h1V))
  have hsne : s.Nonempty := by
    have : (1 : G) ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, -⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨e, rfl⟩ := hsc.exists_eq_range hsne
  have hcov : ∀ x : G, ∃ n, x ∈ U (e n) := by
    intro x
    have : x ∈ ⋃ y ∈ Set.range e, U y := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := this
    exact ⟨n, hn⟩
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, {x | (γ : G) * x ∈ U (e n)}
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_iUnion fun γ => (hUo _).preimage (continuous_const.mul continuous_id)
  have hSmem : ∀ n x, x ∈ S n ↔ ∃ γ : Γ, (γ : G) * x ∈ U (e n) := by
    intro n x; simp [S]
  have hSinv : ∀ n (δ : Γ) x, (δ : G) * x ∈ S n ↔ x ∈ S n := by
    intro n δ x
    rw [hSmem, hSmem]
    constructor
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ, by simpa [mul_assoc] using h⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ⁻¹, by simpa [mul_assoc] using h⟩
  refine ⟨⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ), ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hUo _).measurableSet.inter
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hSo k).measurableSet.compl)
  · intro x
    have hex : ∃ n, x ∈ S n := by
      obtain ⟨n, hn⟩ := hcov x
      exact ⟨n, (hSmem n x).2 ⟨1, by simpa using hn⟩⟩
    have key : ∀ γ : Γ, γ • x ∈ (⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ)) ↔
        (γ : G) * x ∈ U (e (Nat.find hex)) := by
      intro γ
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Subgroup.smul_def, smul_eq_mul, hSinv]
      constructor
      · rintro ⟨n, hn, hk⟩
        have : Nat.find hex = n := by
          rw [Nat.find_eq_iff]
          exact ⟨(hSmem n x).2 ⟨γ, hn⟩, hk⟩
        rw [this]; exact hn
      · intro h
        exact ⟨_, h, fun k hk => Nat.find_min hex hk⟩
    obtain ⟨γ, hγ⟩ := (hSmem _ x).1 (Nat.find_spec hex)
    refine ⟨γ, (key γ).2 hγ, fun δ hδ => ?_⟩
    have hδ' := (key δ).1 hδ
    have := hUinj _ (δ * γ⁻¹) _ hγ (by simpa [mul_assoc] using hδ')
    exact mul_inv_eq_one.1 this

theorem exists_isFundamentalDomain {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) :
    ∃ F : Set G, IsFundamentalDomain Γ F μ := by
  obtain ⟨F, hF, h⟩ := exists_measurable_section Γ
  exact ⟨F, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem exists_fundDom : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure →
    ∃ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ := by
  intro D V μ _
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := (GlobalTheory.RationalCountable.discrete_countable_GQ D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact exists_isFundamentalDomain (GQ V) μ

end GlobalTheory.FundDomDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsResOfTameAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameResidue

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem locK_eq_of_congr (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P)
    (a b : 𝓞 E) (k l : Eˣ) (hk : (k : E) = a) (hl : (l : E) = b) (hb : b ∉ P.asIdeal)
    (hab : a - b ∈ P.asIdeal) : χ.locK P k = χ.locK P l := by
  have ha : a ∉ P.asIdeal := fun ha => hb (by simpa using P.asIdeal.sub_mem ha hab)
  have hva : P.valuation E (k : E) = 1 := by
    rw [hk]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 ha
  have hvb : P.valuation E (l : E) = 1 := by
    rw [hl]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 hb
  have hvd : P.valuation E ((k : E) - l) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : (k : E) - l = algebraMap (𝓞 E) E (a - b) := by rw [hk, hl, map_sub]
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_le_pow_iff_mem (a - b) 1).2 (by simpa using hab)
  have key : χ.locK P (k * l⁻¹) = 1 := by
    refine h (atFin P (k * l⁻¹)) ?_ ?_
    · show Valued.v ((((k * l⁻¹ : Eˣ) : E)) : P.adicCompletion E) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Units.val_mul, Units.val_inv_eq_inv_val, map_mul,
        map_inv₀, hva, hvb]
      simp
    · have e : ((atFin P (k * l⁻¹) : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1
          = algebraMap E (P.adicCompletion E) (((k : E) - l) * (l : E)⁻¹) := by
        have e2 : ((k : E) - l) * (l : E)⁻¹ = ((k * l⁻¹ : Eˣ) : E) - 1 := by
          rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
        rw [e2, map_sub, map_one]
        rfl
      rw [e]
      show Valued.v (((((k : E) - l) * (l : E)⁻¹ : E)) : P.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_mul, map_inv₀, hvb]
      simpa using hvd
  rwa [map_mul, map_inv, mul_inv_eq_one] at key

theorem exists_lift (P : HeightOneSpectrum (𝓞 E)) (u : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ p : 𝓞 E × Eˣ, (p.2 : E) = p.1 ∧ (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ p.1 ∧ p.1 ∉ P.asIdeal := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 E ⧸ P.asIdeal)
  haveI : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have hn : a ∉ P.asIdeal := fun h => u.ne_zero (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
  have h0 : (a : E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    exact hn (this ▸ P.asIdeal.zero_mem)
  exact ⟨(a, Units.mk0 (a : E) h0), rfl, ha.symm, hn⟩

theorem exists_res (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P) :
    ∃ c : (𝓞 E ⧸ P.asIdeal)ˣ →* ℂˣ, ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → c u = χ.locK P k := by
  choose f hf1 hf2 hf3 using exists_lift P
  have main : ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → χ.locK P (f u).2 = χ.locK P k := by
    intro a k u hk hu
    refine (locK_eq_of_congr χ P h a (f u).1 k (f u).2 hk (hf1 u) (hf3 u) ?_).symm
    rw [← Ideal.Quotient.eq, ← hu, ← hf2 u]
  refine ⟨MonoidHom.mk' (fun u => χ.locK P (f u).2) ?_, main⟩
  intro u v
  rw [← map_mul]
  refine main ((f u).1 * (f v).1) _ _ ?_ ?_
  · rw [Units.val_mul, hf1, hf1]; simp
  · rw [Units.val_mul, map_mul, ← hf2, ← hf2]

end GlobalTheory.TameResidue

theorem GlobalTheory.exists_isRes_of_tameAt : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (P : Pl D.host.E),
    χ.TameAt P → ∃ c, IsRes χ P c :=
  fun _ χ P h => GlobalTheory.TameResidue.exists_res χ P h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRestrictedProductTupleMeasure
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_isProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), Conv b mi mv → ∃ ν, IsProd b ν mi mv := by
  intro F E _ _ _ _ _ d b n M mi mv hc
  obtain ⟨hi, hv, hs⟩ := hc
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : Countable (𝓞 F) := Countable.of_equiv _ (RingOfIntegers.basis F).equivFun.symm.toEquiv
  haveI : Countable (Ideal (𝓞 F)) := by
    have hsurj : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) :=
      fun I => (IsNoetherian.noetherian I)
    exact hsurj.countable
  haveI : Countable (HeightOneSpectrum (𝓞 F)) :=
    Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun _ _ h => HeightOneSpectrum.ext h)
  obtain ⟨hint, -⟩ := GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E (AlgHom.id F E) d b
  obtain ⟨hemb, hrange, -, -⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  have hlat : ∀ v, (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
    intro v
    ext Y
    rw [mem_latV_iff]
    simp
  have hcpt : ∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (hint v).1
  have hmeas : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => (hint v).2.measurableSet
  have hsi : SigmaFinite mi := inferInstance
  have hsv : ∀ v, SigmaFinite (mv v) := fun v => by
    haveI := hv v
    infer_instance
  obtain ⟨ν, hν0, hν⟩ := _root_.GlobalTheory.GaugeEx.AbsProd.exists_restricted_product (HeightOneSpectrum (𝓞 F)) _ _ (fun v => latV b v) mi mv hsi hsv hmeas
    (fun v => by haveI := hv v; exact (hcpt v).measure_lt_top.ne) hs
  set e := (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) with he
  have hmap : (ν.comap e).map e = ν := by
    rw [hemb.map_comap, hrange]
    exact Measure.restrict_eq_self_of_ae_mem hν0
  refine ⟨ν.comap e, ⟨hi, hv, hs⟩, fun S fi fv hfi hfv => ?_⟩
  have h := hν S fi fv hfi hfv
  rw [← hmap, hemb.restrict_map, hemb.lintegral_map] at h
  exact h

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnSwap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilSwap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck

variable {D : D7}

def trEquiv (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) : ThS ψ V W ≃ₗ[ℂ] ThS ψ W V where
  toFun Φ := ⟨fun y => Φ.1 y.transpose, mem_ThS.2 (isThetaFun_transpose ψ V W hne _ (mem_ThS.1 Φ.2))⟩
  invFun Φ := ⟨fun x => Φ.1 x.transpose, mem_ThS.2 (isThetaFun_transpose ψ W V hne.symm _ (mem_ThS.1 Φ.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem heis_transpose (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W)
    (f : WA W V → ℂ) :
    (fun x : WA V W => Heisenberg₂ ψ W V u.transpose f x.transpose) = Heisenberg₂ ψ V W u (fun x => f x.transpose) := by
  funext x
  simp only [Heisenberg₂, symplH_transpose V W hne, Matrix.transpose_add]

def swapRep {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) : GA D W × GA D V →* Module.End ℂ (ThS ψ W V) :=
  ((trEquiv ψ hne).conjRingEquiv.toMonoidHom.comp om).comp (MulEquiv.prodComm (M := GA D W) (N := GA D V)).toMonoidHom

theorem swapRep_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) (h : GA D W) (g : GA D V) (Φ : ThS ψ W V) :
    swapRep hne om (h, g) Φ = trEquiv ψ hne (om (g, h) ((trEquiv ψ hne).symm Φ)) := rfl

theorem exists_isWeilOn_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), V.rank ≠ W.rank → IsWeilOn ψ V W χ χ' om → ∃ om' : GA D W × GA D V →* Module.End ℂ (ThS ψ W V), IsWeilOn ψ W V χ' χ om' ∧ ∀ (g : GA D V) (h : GA D W) (Φ : ThS ψ V W) (Φ' : ThS ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) → ∀ x : WA V W, (om' (h, g) Φ').1 x.transpose = (om (g, h) Φ).1 x := by
  intro D ψ _ V W χ χ' om hne H
  refine ⟨swapRep hne om, ⟨fun h g w₀ Φ Φ' e => ?_, fun γ hγ γ' hγ' Φ => ?_, fun Φ w => ?_,
    fun μ 𝓕 hμ h𝓕 p Φ => ?_, fun e he h g hh hg y x hy hx => ?_⟩, fun g h Φ Φ' e x => ?_⟩
  · have k := H.Heisenberg₂ g h w₀.transpose ((trEquiv ψ hne).symm Φ) ((trEquiv ψ hne).symm Φ') (by
      show (fun x : WA V W => Φ'.1 x.transpose) = _
      rw [e]
      exact heis_transpose ψ hne w₀.transpose Φ.1)
    rw [swapRep_apply, swapRep_apply]
    show (fun y : WA W V => (om (g, h) _).1 y.transpose) = _
    rw [k, actHom_swap W V hne.symm]
    exact heis_transpose ψ hne.symm _ _
  · exact H.aut γ' hγ' γ hγ ((trEquiv ψ hne).symm Φ)
  · exact (H.cont ((trEquiv ψ hne).symm Φ) w.transpose).comp continuous_swap
  · haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA W V) := Pi.topologicalAddGroup
    haveI : BorelSpace (WA V W) := ⟨rfl⟩
    haveI : BorelSpace (WA W V) := ⟨rfl⟩
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WA W V)
      (Matrix.transposeAddEquiv _ _ _) continuous_id.matrix_transpose continuous_id.matrix_transpose
      (ratL V W) (ratL W V) (fun x => ⟨fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩,
        fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩⟩) μ 𝓕 hμ h𝓕
    rw [← h3 fun w => ‖(swapRep hne om p Φ).1 w‖ ^ 2, ← h3 fun w => ‖Φ.1 w‖ ^ 2]
    exact H.unit ν _ h1 h2 (p.2, p.1) ((trEquiv ψ hne).symm Φ)
  · obtain ⟨r, hr, k⟩ := H.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ Φ => ?_⟩
    rw [splitFac_swap V W hne]
    exact k (ℓ.comp (trEquiv ψ hne).toLinearMap) (fun u hu Ψ Ψ' e' =>
      hℓ u.transpose (fun i j => hu j i) (trEquiv ψ hne Ψ) (trEquiv ψ hne Ψ') (by
        show (fun y : WA W V => Ψ'.1 y.transpose) = _
        rw [e']
        exact heis_transpose ψ hne.symm u.transpose Ψ.1)) ((trEquiv ψ hne).symm Φ)
  · have : (trEquiv ψ hne).symm Φ' = Φ := Subtype.ext (funext e)
    rw [swapRep_apply, this]
    rfl

end GlobalTheory.Mem.WeilSwap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletionStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  first | exact @GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | exact GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | (intros; apply GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfFam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.InfFamUnique

theorem existsUnique_infFam : ∀ D : D7, ∃! θ : InfF D, IsInfFam θ := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  exact ⟨θ, hθ, fun θ' h' => funext fun ρ =>
    GlobalTheory.Mem.VolEmb.infEmb_unique (tauE D ρ) (θ' ρ) (θ ρ) (h' ρ) (hθ ρ)⟩

end GlobalTheory.Mem.InfFamUnique
end
end

