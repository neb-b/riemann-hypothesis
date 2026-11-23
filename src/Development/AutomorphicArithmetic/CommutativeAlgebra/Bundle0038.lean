module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0017
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0028
public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0037
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0003
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0036
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OffDiagonalContinuationInductive
public import Development.EtaleCohomology.WeilConjectures.EmptyVan2
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMappingConeSemiMapOfInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.acy_mappingCone_semiMap_of_injective :
    ∀ (R : Type) [CommRing R] (L B : Cx R), (∀ s, Injective (L.X s)) → (∀ s, Injective (B.X s)) → ∀ (ρ : SemiMap L B) (Q : Scheme.{0} → Prop) (s : ℤ), Acy Q ((mappingCone ρ.toZ).X s) := by
  intro R _ L B hL hB ρ Q s
  have key : ∀ (I : Shv R), Injective I → Acy Q ((restr (Int.castRingHom R)).obj I) := by
    intro I hI P _ n hn
    exact UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology _ P n (GlobalTheory.T.restrictScalars_injective_sheaf_acyclic ℤ R _ I P n hn)
  exact UpperTheory.acy_middle_of_shortExact Q _ (mappingCone.triangleRotateShortComplexSplitting ρ.toZ s).shortExact
    (key _ (hB s)) (key _ (hL (s + 1)))
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteSurjectiveCurveCoverOfFunctionFieldE
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4
open GroundTheory.Heights₂.Heights.Model (genericSpecMap)

private theorem objIso {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F] [Algebra C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] [Algebra Γ(C, U) F]
    [IsScalarTower Γ(C, U) C.functionField F] :
    ∃ E : Γ((genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization ⁻¹ᵁ U) ≅
        CommRingCat.of (integralClosure Γ(C, U) F),
      (genericSpecMap C F).fromNormalization.app U ≫ E.hom =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) := by
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hmem : genericSpecMap C F (IsLocalRing.closedPoint F) ∈ U := by
    rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_closedPoint]
    exact hη
  have key := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_app_iso C F U hη hmem
  letI : Algebra Γ(C, U) Γ(Spec (CommRingCat.of F), genericSpecMap C F ⁻¹ᵁ U) :=
    ((genericSpecMap C F).app U).hom.toAlgebra
  let eR := ((Spec (CommRingCat.of F)).presheaf.mapIso (eqToIso
    (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of F), genericSpecMap C F ⁻¹ᵁ U) ≃ₐ[Γ(C, U)] F :=
    AlgEquiv.ofRingEquiv (f := eR) fun x => by
      rw [IsScalarTower.algebraMap_apply Γ(C, U) C.functionField F]
      exact congrArg (fun φ => φ.hom x) key
  refine ⟨(genericSpecMap C F).normalizationObjIso hU ≪≫
    eA.mapIntegralClosure.toRingEquiv.toCommRingCatIso, ?_⟩
  rw [(genericSpecMap C F).fromNormalization_app hU]
  rw [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext x
  exact eA.commutes x

private theorem isFin {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} [IsIntegral C]
    (c : C ⟶ Sp Ω) [LocallyOfFiniteType c] (F : Type) [Field F] [Algebra C.functionField F]
    [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)] :
    IsFinite (genericSpecMap C F).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hN : (U : Set C).Nonempty
  · haveI : Nonempty U := ⟨⟨hN.some, hN.some_mem⟩⟩
    haveI : IsFractionRing Γ(C, U) C.functionField :=
      functionField_isFractionRing_of_isAffineOpen C U hU
    letI : Algebra Ω Γ(C, U) := (GlobalTheory.NormCurve.constHom c U).toAlgebra
    haveI : Algebra.FiniteType Ω Γ(C, U) := GlobalTheory.NormCurve.finiteType_constHom c hU
    letI : Algebra Γ(C, U) F :=
      ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
    haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Module.Finite Γ(C, U) (integralClosure Γ(C, U) F) :=
      UpperTheory.module_finite_integralClosure_finiteExt_perfect Ω Γ(C, U) C.functionField F
    obtain ⟨E, hE⟩ := objIso F U hU
    have h1 : (genericSpecMap C F).fromNormalization.app U =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) ≫ E.inv := by
      rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h1, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun y => ⟨E.hom y, ?_⟩)
      (RingHom.finite_algebraMap.mpr inferInstance)
    simp
  · have hb : U = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.mp hN)
    subst hb
    have hb' : (genericSpecMap C F).fromNormalization ⁻¹ᵁ (⊥ : C.Opens) = ⊥ := by simp
    haveI : Subsingleton Γ((genericSpecMap C F).normalization,
        (genericSpecMap C F).fromNormalization ⁻¹ᵁ (⊥ : C.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal
        ((genericSpecMap C F).normalization.sheaf.isTerminalOfEqEmpty hb')
    exact RingHom.Finite.of_surjective _ fun y => ⟨0, Subsingleton.elim _ _⟩

private theorem stalkClosed {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F]
    [Algebra C.functionField F] [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    (y : (genericSpecMap C F).normalization) :
    IsIntegrallyClosed ((genericSpecMap C F).normalization.presheaf.stalk y) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (genericSpecMap C F).fromNormalization y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  letI : Algebra Γ(C, U) F :=
    ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
  haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsIntegrallyClosed (integralClosure Γ(C, U) F) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension C.functionField
  obtain ⟨E, -⟩ := objIso F U hU
  have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
    hU.preimage (genericSpecMap C F).fromNormalization
  have hy : y ∈ (genericSpecMap C F).fromNormalization ⁻¹ᵁ U := hxU
  letI iA := TopCat.Presheaf.algebra_section_stalk (genericSpecMap C F).normalization.presheaf
    (⟨y, hy⟩ : (genericSpecMap C F).fromNormalization ⁻¹ᵁ U)
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  let e := E.commRingCatIsoToRingEquiv
  letI : Algebra (integralClosure Γ(C, U) F) ((genericSpecMap C F).normalization.presheaf.stalk y) :=
    ((algebraMap _ _).comp e.symm.toRingHom).toAlgebra
  haveI := IsLocalization.isLocalization_of_base_ringEquiv
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    ((genericSpecMap C F).normalization.presheaf.stalk y) e
  refine isIntegrallyClosed_of_isLocalization (R := integralClosure Γ(C, U) F) _
    (Submonoid.map e (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
    (le_nonZeroDivisors_of_noZeroDivisors ?_)
  rintro ⟨x, hx, hx0⟩
  rw [map_eq_zero_iff e e.injective] at hx0
  subst hx0
  exact hx (Ideal.zero_mem _)

private theorem dimOne {Ω : Type} [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω)
    (hc : IsCurve c) (F : Type) [Field F]
    [Algebra C.functionField F] [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    [IsFinite (genericSpecMap C F).fromNormalization] :
    topologicalKrullDim (genericSpecMap C F).normalization = 1 := by
  obtain ⟨p0⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have hemb := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
    (e := (id : (genericSpecMap C F).normalization → (genericSpecMap C F).normalization))
    Topology.IsEmbedding.id (Z := Set.univ) Set.range_id
  rw [← hemb]
  refine GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := Set.univ)
    ⟨(genericSpecMap C F).toNormalization p0, trivial⟩ fun y _ => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (genericSpecMap C F).fromNormalization y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  letI : Algebra Γ(C, U) F :=
    ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
  haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨E, -⟩ := objIso F U hU
  have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
    hU.preimage (genericSpecMap C F).fromNormalization
  refine ⟨((genericSpecMap C F).fromNormalization ⁻¹ᵁ U : Set _),
    ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U).isOpen, hxU, ?_⟩
  have hinj : Function.Injective (algebraMap Γ(C, U) F) :=
    (algebraMap C.functionField F).injective.comp (IsFractionRing.injective Γ(C, U) C.functionField)
  haveI : FaithfulSMul Γ(C, U) (integralClosure Γ(C, U) F) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b h => hinj (congrArg Subtype.val h)
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
    (by rw [hV.range_fromSpec, Set.inter_univ])]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    Γ((genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization ⁻¹ᵁ U)).trans ?_
  rw [ringKrullDim_eq_of_ringEquiv E.commRingCatIsoToRingEquiv,
    GlobalTheory.ringKrullDim_eq_of_isIntegral Γ(C, U) (integralClosure Γ(C, U) F),
    CurveCut.CoverPf.krullDim_eq_one c hc U hU ⟨_, hxU⟩]
  rfl

private theorem surjNorm {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F]
    [Algebra C.functionField F] [QuasiCompact (genericSpecMap C F)]
    [QuasiSeparated (genericSpecMap C F)] : Surjective (genericSpecMap C F).fromNormalization := by
  constructor
  have hcl : IsClosedMap (genericSpecMap C F).fromNormalization :=
    (genericSpecMap C F).fromNormalization.isClosedMap
  have hη : genericPoint C ∈ Set.range (genericSpecMap C F).fromNormalization := by
    have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_closedPoint C F
    rw [← Scheme.Hom.toNormalization_fromNormalization (genericSpecMap C F)] at h
    exact ⟨_, h⟩
  have hsub : closure ({genericPoint C} : Set C) ⊆ Set.range (genericSpecMap C F).fromNormalization :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hcl.isClosed_range
  intro x
  exact hsub (specializes_iff_mem_closure.mp (genericPoint_specializes x))

private theorem restrictSquare {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens}
    (hU : IsAffineOpen U) :
    (f ∣_ U) ≫ hU.isoSpec.hom = (hU.preimage f).isoSpec.hom ≫ Spec.map (f.app U) := by
  rw [← cancel_mono hU.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, Category.assoc, Scheme.Hom.app_eq_appLE,
    IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl,
    ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem UpperTheory.exists_finite_surjective_curve_cover_of_functionField_extension :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
        ∀ (hI : IsIntegral C) (F : Type) [Field F] [Algebra C.functionField F] [FiniteDimensional C.functionField F],
        ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧
          ∀ (U : C.Opens) (hU : IsAffineOpen U) (_ : Nonempty U) (_ : Algebra Γ(C, U) F) (_ : IsScalarTower Γ(C, U) C.functionField F),
          ∃ e : (γ ⁻¹ᵁ U).toScheme ≅ Sp (integralClosure Γ(C, U) F),
            (γ ∣_ U) ≫ hU.isoSpec.hom = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F))) := by
  intro Ω _ _ C c hc hI F _ _ _
  haveI : IsProper c := hc.2.1
  haveI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
  haveI : IsFinite (genericSpecMap C F).fromNormalization := isFin c F
  refine ⟨(genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization,
    ⟨inferInstance, inferInstance, ?_⟩, surjNorm F, inferInstance, ?_⟩
  · exact UpperTheory.smooth_of_normal_curve_perfectField Ω ((genericSpecMap C F).fromNormalization ≫ c) inferInstance inferInstance
      (stalkClosed F) (dimOne c hc F)
  · intro U hU hne alg tower
    haveI := hne
    letI := alg
    haveI := tower
    obtain ⟨E, hE⟩ := objIso F U hU
    have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
      hU.preimage (genericSpecMap C F).fromNormalization
    refine ⟨hV.isoSpec ≪≫ Scheme.Spec.mapIso E.symm.op, ?_⟩
    rw [restrictSquare _ hU, Iso.trans_hom, Category.assoc]
    congr 1
    have h2 : (genericSpecMap C F).fromNormalization.app U =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) ≫ E.inv := by
      rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h2, Spec.map_comp]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsH1MuGlueOfCompatible
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.MuCohomologyGluing

private theorem sub_empty (q : ℕ) (Y : Scheme.{0}) [IsEmpty Y] (n i : ℤ) :
    Subsingleton (Ht q (sch.obj Y) n i) := by
  have e : Y ≅ ⊥_ Scheme.{0} := (isInitialOfIsEmpty (X := Y)).uniqueUpToIso initialIsInitial
  exact LateralTheory.EtaleTrace.H_sub (ZMod q) Y
    (LateralTheory.EWeil.EmptyVan₂.isZero_free.of_iso ((free (ZMod q)).mapIso (yoneda.mapIso e))) (tw q i) n

private theorem pl_le (q : ℕ) {X : Scheme.{0}} {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (h3 : A ≤ C)
    (z : Ht q (sch.obj C) 1 1) :
    pl q 1 (X.homOfLE h1) 1 (pl q 1 (X.homOfLE h2) 1 z) = pl q 1 (X.homOfLE h3) 1 z := by
  rw [← pl_comp, Scheme.homOfLE_homOfLE]

private theorem van (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X] (hζ : Nonempty (Prim q Γ(X, ⊤)))
    (hq : IsUnit (q : Γ(X, ⊤))) (n : ℕ) (A : Fin n → X.Opens) (P : X.Opens) (hP : P ≤ ⨆ i, A i)
    (d : Ht q (sch.obj P) 1 1)
    (hd : ∀ i, pl q 1 (X.homOfLE (inf_le_right : A i ⊓ P ≤ P)) 1 d = 0) : d = 0 := by
  have hmem : ∀ x : P.toScheme, P.ι x ∈ P := fun x => by
    rw [← SetLike.mem_coe, ← P.range_ι]
    exact ⟨x, rfl⟩
  by_cases hne : Nonempty P.toScheme
  · haveI : IsIntegral P.toScheme := isIntegral_of_isOpenImmersion P.ι
    have hζ' : Nonempty (Prim q Γ(P.toScheme, ⊤)) := hζ.map (Prim.map P.ι.appTop.hom)
    have hq' : IsUnit (q : Γ(P.toScheme, ⊤)) := by simpa using hq.map P.ι.appTop.hom
    have key := UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero q P.toScheme hζ' hq' n (fun i => P.ι ⁻¹ᵁ A i) ⊤ (by
      intro x _
      have hx : P.ι x ∈ ⨆ i, A i := hP (hmem x)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩) d (fun i => by
        have e : P.ι ⁻¹ᵁ A i ≤ P.ι ⁻¹ᵁ (A i ⊓ P) := by
          intro x hx
          exact ⟨hx, hmem x⟩
        have w : P.ι.resLE (A i ⊓ P) (P.ι ⁻¹ᵁ A i) e ≫ X.homOfLE (inf_le_right : A i ⊓ P ≤ P) =
            (P.ι ⁻¹ᵁ A i).ι := by
          rw [← cancel_mono P.ι]
          simp
        rw [← w, pl_comp, hd i, map_zero])
    have w : P.toScheme.topIso.inv ≫ (⊤ : P.toScheme.Opens).ι = 𝟙 _ := P.toScheme.topIso.inv_hom_id
    have := congrArg (pl q 1 P.toScheme.topIso.inv 1) key
    rw [← pl_comp, w, map_zero] at this
    simpa [pl, pull_id] using this
  · haveI : IsEmpty P.toScheme := not_nonempty_iff.1 hne
    haveI := sub_empty q P.toScheme 1 1
    exact Subsingleton.elim _ _

end UpperTheory.Cb.MuCohomologyGluing

open UpperTheory.Cb.MuCohomologyGluing in
theorem UpperTheory.exists_h1Mu_glue_of_compatible :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (x : ∀ i, Ht q (sch.obj (U i)) 1 1), (∀ i j, pl q 1 (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) 1 (x i) = pl q 1 (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) 1 (x j)) → ∃ y : Ht q (sch.obj (⨆ i, U i : X.Opens)) 1 1, ∀ i, pl q 1 (X.homOfLE (le_iSup U i)) 1 y = x i := by
  intro q _ X _ hζ hq n
  induction n with
  | zero =>
    intro U x _
    exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro U x hx
    set W : X.Opens := ⨆ i : Fin n, U i.castSucc with hW
    have hAW : ∀ i : Fin n, U i.castSucc ≤ W := fun i => le_iSup (fun i : Fin n => U i.castSucc) i
    obtain ⟨y, hy⟩ : ∃ y : Ht q (sch.obj W) 1 1, ∀ i : Fin n, pl q 1 (X.homOfLE (hAW i)) 1 y = x i.castSucc :=
      ih (fun i => U i.castSucc) (fun i => x i.castSucc) (fun i j => hx _ _)
    set B : X.Opens := U (Fin.last n) with hB
    have c : UpperTheory.Cb.OffDiagonalContinuation.Sq W B (W ⊔ B) (W ⊓ B) := ⟨rfl, rfl⟩
    obtain ⟨dd, hdd, -⟩ := UpperTheory.Cb.OffDiagonalContinuation.mv q 1
    have hex := (hdd c 1).2.2
    have d0 : pl q 1 (X.homOfLE (inf_le_left : W ⊓ B ≤ W)) 1 y -
        pl q 1 (X.homOfLE (inf_le_right : W ⊓ B ≤ B)) 1 (x (Fin.last n)) = 0 := by
      refine van q X hζ hq n (fun i => U i.castSucc) (W ⊓ B) inf_le_left _ (fun i => ?_)
      have h1 : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc ⊓ B := inf_le_inf_left _ inf_le_right
      rw [map_sub, pl_le q _ _ (inf_le_right.trans inf_le_left), pl_le q _ _ (inf_le_right.trans inf_le_right),
        ← pl_le q (inf_le_left : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc) (hAW i),
        ← pl_le q h1 (inf_le_right : U i.castSucc ⊓ B ≤ B), hy i, ← hx i.castSucc (Fin.last n),
        pl_le q h1 inf_le_left inf_le_left, sub_self]
    obtain ⟨z, hz⟩ := (hex (y, x (Fin.last n))).1 d0
    have hz1 : pl q 1 (X.homOfLE (le_sup_left : W ≤ W ⊔ B)) 1 z = y := congrArg Prod.fst hz
    have hz2 : pl q 1 (X.homOfLE (le_sup_right : B ≤ W ⊔ B)) 1 z = x (Fin.last n) := congrArg Prod.snd hz
    have hle : (⨆ i, U i : X.Opens) ≤ W ⊔ B := by
      refine iSup_le fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact le_sup_right
      · exact (hAW j).trans le_sup_left
    refine ⟨pl q 1 (X.homOfLE hle) 1 z, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [pl_le q _ _ le_sup_right, hz2]
    · rw [pl_le q _ _ ((hAW j).trans le_sup_left), ← pl_le q (hAW j) (le_sup_left : W ≤ W ⊔ B), hz1]
      exact hy j
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonCohomologyClassChainsOfAcyLocallyExa
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_cohomologyClass_chains_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (E : Spc), (∀ s, Acy (fun U => Nonempty (Sx E 0 U)) (C.X s)) → (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ n : ℤ, Subsingleton (CohomologyClass ((chains ℤ).obj E) C n) := by
  intro C a _ E hAcy hLoc n
  haveI : IsStrictlyLE ((chains ℤ).obj E) 0 := (GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta ℤ).1 E
  refine UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift ((chains ℤ).obj E) C a ?_ n
  intro p j f hf
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hp
    have hmono : ∀ {V U : Scheme.{0}} (g : V ⟶ U), Nonempty (Sx E 0 U) → Nonempty (Sx E 0 V) := by
      intro V U g hx
      obtain ⟨x⟩ := hx
      exact ⟨((E.obj (op (SimplexCategory.mk 0))).map g.op) x⟩
    have hsupp : Supp (fun U => Nonempty (Sx E 0 U)) (E.obj (op (SimplexCategory.mk m))) := by
      intro U hx
      obtain ⟨x⟩ := hx
      exact ⟨((E.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m) 0).op).app (op U)) x⟩
    have hf' : ((chainsXIso ℤ E m).inv ≫ f) ≫ C.d j (j + 1) = 0 := by
      rw [Category.assoc, hf, comp_zero]
    obtain ⟨g, hg⟩ := UpperTheory.exists_primitive_free_of_acy_locally_exact C a (fun U => Nonempty (Sx E 0 U)) hmono hAcy hLoc
      (E.obj (op (SimplexCategory.mk m))) hsupp j _ hf'
    refine ⟨(chainsXIso ℤ E m).hom ≫ g, ?_⟩
    rw [Category.assoc, hg, Iso.hom_inv_id_assoc]
  · refine ⟨0, ?_⟩
    have hz : IsZero (((chains ℤ).obj E).X p) :=
      ((chains ℤ).obj E).isZero_of_isStrictlyLE 0 p hp
    rw [zero_comp]
    exact (hz.eq_of_src _ _).symm
end

