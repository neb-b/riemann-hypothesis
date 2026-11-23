module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureInverseInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUniformizerTorusTranslateUnipotentQuoti
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace ChangeVar

theorem locallyCompact_GA_chv : LocallyCompactSpace (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GA_chv : SecondCountableTopology (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_NA : IsClosed ((NA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have hv : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
  have : ((NA E n : Subgroup (GA E n)) : Set (GA E n)) =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩
      ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact GlobalTheory.SmGL.mem_unipB (Ad E)
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun i => ?_)
  · exact isClosed_eq (hv.matrix_elem i j) continuous_const
  · exact isClosed_eq (hv.matrix_elem i i) continuous_const

theorem NE_le_NA : NE E n ≤ NA E n := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hu
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i j) = 0
    rw [h1 i j hij, map_zero]
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i i) = 1
    rw [h2 i, map_one]

theorem countable_NE : Countable (NE E n) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  exact ((Set.countable_range (ratGL E n)).mono (by rintro _ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)).to_subtype

theorem tl_inv_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {u : GA E n} (hu : u ∈ NA E n) :
    (tl n ϖ l)⁻¹ * u * tl n ϖ l ∈ NA E n := by
  have h := diagT_conj_mem (n := n) (R := Ad E)
    (fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)))⁻¹ hu
  rw [map_inv, inv_inv, ← tl_eq_diagT] at h
  exact h

end ChangeVar

open ChangeVar

theorem lintegral_tl_inv_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  intro E _ _ n _ _ μ _ ϖ hϖ l 𝓕 h𝓕 F hF hinv
  haveI : LocallyCompactSpace (GA E n) := locallyCompact_GA_chv
  haveI : SecondCountableTopology (GA E n) := secondCountable_GA_chv
  haveI : SigmaCompactSpace (GA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := inferInstance
  haveI : MeasurableMul₂ (GA E n) := inferInstance
  haveI : MeasurableInv (GA E n) := inferInstance
  haveI : LocallyCompactSpace (NA E n) := isClosed_NA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (NA E n) :=
    isClosed_NA.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaCompactSpace (NA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := countable_NE (E := E) (n := n)
  set ν : Measure (NA E n) := Measure.haar with hν
  haveI : ν.IsInvInvariant := _root_.GlobalTheory.CellDec.NA_isInvInvariant E n ν
  set_option synthInstance.maxHeartbeats 200000 in
    haveI : SFinite ν := inferInstance
  obtain ⟨D, hD, hD0, hDtop⟩ := _root_.GlobalTheory.CellDec.exists_fundamentalDomain_NE E n ν
  set t := tl n ϖ l with ht

  let cM : NA E n ≃* NA E n :=
    { toFun := fun u => ⟨t * u * t⁻¹, tl_conj_mem ϖ l u.2⟩
      invFun := fun u => ⟨t⁻¹ * u * t, tl_inv_conj_mem ϖ l u.2⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcM : ∀ u : NA E n, ((cM u : NA E n) : GA E n) = t * u * t⁻¹ := fun _ => rfl
  let c : NA E n ≃ᵐ NA E n :=
    { toEquiv := cM.toEquiv
      measurable_toFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk
      measurable_invFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk }
  have hmod : ∀ A, MeasurableSet A → ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := by
    intro A hA
    rw [← _root_.GlobalTheory.CellDec.ModulusPf.modulus_conj E n ν ϖ hϖ l A hA]
    congr 1
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨a, ha, hau⟩
      convert ha
      exact Subtype.ext hau.symm
  have hmap : Measure.map c ν = ENNReal.ofReal (dinv n l) • ν := by
    ext A hA
    rw [Measure.map_apply c.measurable hA, hmod A hA, Measure.smul_apply, smul_eq_mul]
  have hmod' : ∀ A, ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := fun A => by
    rw [← c.map_apply, hmap, Measure.smul_apply, smul_eq_mul]

  set Γ : Subgroup (NA E n) := (NE E n).subgroupOf (NA E n) with hΓ
  set Γ' : Subgroup (NA E n) := Γ.comap cM.toMonoidHom with hΓ'
  have hΓmap : Γ.map (NA E n).subtype = NE E n := by
    rw [hΓ, Subgroup.subgroupOf_map_subtype, inf_of_le_left NE_le_NA]
  have hmemΓ' : ∀ x : GA E n, x ∈ Γ'.map (NA E n).subtype ↔ t * x * t⁻¹ ∈ NE E n := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hy)
    · intro hx
      have hxN : x ∈ NA E n := by
        have := tl_inv_conj_mem ϖ l (NE_le_NA hx)
        rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this
      exact ⟨⟨x, hxN⟩, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  haveI : Countable Γ := Function.Injective.countable (f := fun g : Γ => (⟨(g : NA E n), g.2⟩ : NE E n))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : NE E n => (z : GA E n)) h))
  haveI : Countable Γ' := Function.Injective.countable (f := fun g : Γ' => (⟨cM g, g.2⟩ : Γ))
    fun a b h => Subtype.ext (cM.injective (congrArg (fun z : Γ => (z : NA E n)) h))

  have hD' : IsFundamentalDomain Γ' (c ⁻¹' D) ν := by
    have hsymm : ∀ u : NA E n, ((cM.symm u : NA E n) : GA E n) = t⁻¹ * u * t := fun _ => rfl
    have hc : ∀ u : NA E n, c u = cM u := fun _ => rfl
    refine hD.preimage_of_equiv (f := c) ⟨c.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
      (e := fun g : Γ => (⟨cM.symm g, Subgroup.mem_comap.2 (by
          rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact g.2)⟩ : Γ'))
      ⟨fun a b h => Subtype.ext (cM.symm.injective (congrArg (fun z : Γ' => (z : NA E n)) h)),
        fun g => ⟨⟨cM g, g.2⟩, Subtype.ext (by simp only [MulEquiv.symm_apply_apply])⟩⟩ ?_
    intro g x
    apply Subtype.ext
    simp only [Subgroup.smul_def, smul_eq_mul, hc, hcM, hsymm, Subgroup.coe_mul]
    group
  have h𝓕Γ : IsFundamentalDomain (Γ.map (NA E n).subtype) 𝓕 μ := by rw [hΓmap]; exact h𝓕
  have h𝓕' : IsFundamentalDomain (Γ'.map (NA E n).subtype) ((fun g => t * g) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (f := fun g => t * g) (measurePreserving_mul_left μ t).quasiMeasurePreserving
      (e := fun g : NE E n => (⟨t⁻¹ * g * t, (hmemΓ' _).2 (by convert g.2 using 1; group)⟩ : Γ'.map (NA E n).subtype))
      ⟨fun a b h => Subtype.ext (by
          have h' := congrArg (fun z : Γ'.map (NA E n).subtype => t * (z : GA E n) * t⁻¹) h
          simpa [mul_assoc] using h'),
        fun y => ⟨⟨t * y * t⁻¹, (hmemΓ' y).1 y.2⟩, Subtype.ext (by simp only; group)⟩⟩ ?_
    intro g x
    change t * ((t⁻¹ * g * t) * x) = (g : GA E n) * (t * x)
    group
  have key := _root_.GlobalTheory.CellCompare.lintegral_comparison μ (NA E n) ν Γ Γ' D (c ⁻¹' D) hD hD' 𝓕 ((fun g => t * g) ⁻¹' 𝓕) h𝓕Γ h𝓕' F hF
    (fun h g => hinv h h.2 g)
  rw [hmod'] at key
  have hchg : ∫⁻ g in 𝓕, F (t⁻¹ * g) ∂μ = ∫⁻ g in (fun g => t * g) ⁻¹' 𝓕, F g ∂μ := by
    rw [← (measurePreserving_mul_left μ t).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulLeft t).measurableEmbedding (fun b => F (t⁻¹ * b)) 𝓕]
    simp only [inv_mul_cancel_left]
  rw [hchg]
  refine ((ENNReal.mul_right_inj hD0.ne' hDtop.ne).1 ?_)
  rw [← key]
  ring

end GlobalTheory.CellDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmitted
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmittedPartOne

theorem all_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1
  have h54 := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  have hA := (_root_.GlobalTheory.LiftAdmitted.all_admitted D HW F Cm).1
  refine ⟨hU.1, hU.2.2.1, _root_.GlobalTheory.res_cor_H1f D HW F, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    GlobalTheory.AdmHerrLocal.main D HW F, hU.2.2.2, archimedean_signature_matching_of_liftingTheory D HW F 23 32 32 10 h54,
    lifting_input_five_of_lifting D HW F 10 23 32 32 h54, lifting_input_six_of_lifting D HW F 10 23 32 32 h54,
    _root_.GlobalTheory.elementDenominator_adm7 D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D, GlobalTheory.Per.StrictAdm.strict_adm D, _root_.GlobalTheory.Per.ResFinite.adm12_elementDenominator D⟩

end GlobalTheory.AdmittedPartOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremCHypothesesAdmitted
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremCAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      RamifiedCoefficientChains.admitted D HW F Cm 10 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1
  have h54 := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  have h6a := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  exact ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2,
    RamifiedCoefficientChains.sizes_bound_of_log_estimates D HW F h54, RamifiedCoefficientChains.restriction_dimension_of_division D HW F h54, RamifiedCoefficientChains.level_tools_of_admitted D HW F h54, RamifiedCoefficientChains.lemma_M_prime_hypothesis D HW F h54,
    RamifiedCoefficientChains.crystalline_lift_of_theorem_c D HW F h54, RamifiedCoefficientChains.lifting_bounds_of_theorem_c D HW F h54,
    _root_.GlobalTheory.Per.DcrisExact.fontaine_dcris D, _root_.GlobalTheory.blochKatoDim_at_every_local_situation D, _root_.GlobalTheory.h1f_generators_of_record D,
    Formalism.MainNotions.N.herr_description_H1_of_herr D HW F h6a, _root_.GlobalTheory.ExtCrysCrit.blochKato_ext_all D,
    GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F,
    Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F h6a,
    _root_.GlobalTheory.adm18_of_N1used D HW F Cm (_root_.GlobalTheory.NL.wach_used_clauses D HW F Cm),
    _root_.GlobalTheory.GenCountUnram.admGenL_all D⟩

end GlobalTheory.TheoremCAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremEHypothesesAdmitted
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.AdmThmE

theorem admitted_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.admitted D HW F Cm 10 := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨hU, hE⟩ := _root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm
  obtain ⟨pL, pW, _, _, pWR, pH, pTr, _⟩ := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  obtain ⟨_, hSatE, _, _, _, _, hKillE, _, hF1E, _, hF2E, hTools, hBC⟩ := _root_.GlobalTheory.ArcTools.arc_tools_from_clauses D HW F Cm
  obtain ⟨p1, _, _, _, _, _, _, p8, p9, _, _, a, _⟩ := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  have hX := GlobalTheory.HerrExtUnit.main D HW F
  exact ⟨hU, pL, pW, pWR, pH, pTr, hTools, hSatE, hF1E, hF2E, hKillE, _root_.GlobalTheory.GenCountUnram.admGenL_all D, hBC,
    GlobalTheory.HodgeCrysSeq.hodge_crystalline_sequences D, hE,
    Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hX⟩,
    Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hX⟩⟩

end GlobalTheory.AdmThmE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_of_rec_literal : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  first | exact @GlobalTheory.LocLanglands.isRec_of_isRecLit | exact GlobalTheory.LocLanglands.isRec_of_isRecLit | (intros; apply GlobalTheory.LocLanglands.isRec_of_isRecLit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypotheses
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.NQ

theorem relay_and_arc_inputs : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨_, _, p3, p4, p5, _, _, _, p9, _⟩ := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  obtain ⟨_, _, hW1, _, _, hH, hTr, _⟩ := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  obtain ⟨hSat, _, _, _, _, _, _, hF1, _, hF2, _⟩ := _root_.GlobalTheory.ArcTools.arc_tools_from_clauses D HW F Cm
  exact ⟨UnusedSlot80.relay_general_statement D HW F ⟨p5, p9, hH, hTr, hSat, hF1, hF2⟩,
    ⟨p3, p4, p5, p9, hH, hTr, hW1, hSat⟩⟩

end GlobalTheory.NQ
end

