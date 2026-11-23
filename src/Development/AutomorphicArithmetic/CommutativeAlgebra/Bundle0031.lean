module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.EtaleCohomology.EtaleSheaves.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.Cover2Loc

private def sumP (A B : PSh) : PSh where
  obj T := A.obj T ⊕ B.obj T
  map h := TypeCat.ofHom (Sum.map (A.map h) (B.map h))
  map_id T := by
    ext x
    cases x <;> simp
  map_comp h k := by
    ext x
    cases x <;> simp

private def sumD {A B C : PSh} (a : A ⟶ C) (b : B ⟶ C) : sumP A B ⟶ C where
  app T := TypeCat.ofHom (Sum.elim (a.app T) (b.app T))
  naturality S T h := by
    ext x
    cases x with
    | inl x => exact NatTrans.naturality_apply a h x
    | inr x => exact NatTrans.naturality_apply b h x

private theorem map_comp_gen (R : Type) [CommRing R] {P C : PSh} (c : P ⟶ C) {M : Shv R}
    (p : (free R).obj C ⟶ M) (T : Scheme.{0}) (x : P.obj (op T)) :
    Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R C T (c.app (op T) x)) := by
  have h4 := (GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 C c T x
  show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _
  rw [h4]

private theorem epi_desc (R : Type) [CommRing R] {A B C : PSh} (a : A ⟶ C) (b : B ⟶ C)
    (h : ∀ (T : Scheme.{0}) (y : C.obj (op T)), Loc T fun W k =>
      (∃ x, a.app (op W) x = C.map k.op y) ∨ (∃ x, b.app (op W) x = C.map k.op y)) :
    Epi (biprod.desc ((free R).map a) ((free R).map b)) := by
  haveI : Epi ((free R).map (sumD a b)) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD a b)).2.1 fun T y => ?_
    obtain ⟨S, hS, hP⟩ := h T y
    refine ⟨S, hS, fun W k hk => ?_⟩
    rcases hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩
  constructor
  intro M p q hpq
  have h1 : (free R).map a ≫ p = (free R).map a ≫ q := by
    simpa using biprod.inl ≫= hpq
  have h2 : (free R).map b ≫ p = (free R).map b ≫ q := by
    simpa using biprod.inr ≫= hpq
  apply (cancel_epi ((free R).map (sumD a b))).1
  apply (GlobalTheory.T.free_sections_ext_res_map R (sumP A B) M).2.1
  intro T x
  rw [map_comp_gen, map_comp_gen]
  cases x with
  | inl x =>
    show Sec.map p (freeGen R C T (a.app (op T) x)) = Sec.map q (freeGen R C T (a.app (op T) x))
    rw [← map_comp_gen, ← map_comp_gen, h1]
  | inr x =>
    show Sec.map p (freeGen R C T (b.app (op T) x)) = Sec.map q (freeGen R C T (b.app (op T) x))
    rw [← map_comp_gen, ← map_comp_gen, h2]

end UpperTheory.Cover2Loc

theorem UpperTheory.mayerVietorisCover_of_mono_of_zariskiLocal :
    ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
        (∀ (k : ℕ) (T : Scheme.{0}) (y : Sx E k T), Loc T fun W h => (∃ x : Sx U k W, x.map f = y.res h) ∨ (∃ x : Sx V k W, x.map g = y.res h)) →
        Cover2 R f g := by
  intro R _ U V E f g hf hg hl
  refine ⟨hf, hg, fun n => ?_⟩
  induction n using Opposite.rec with
  | op n =>
    induction n using SimplexCategory.rec with
    | mk k => exact UpperTheory.Cover2Loc.epi_desc R _ _ fun T y => hl k T y
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.NonemptyIsoRelativeEtaleFamilyBaseChange
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

private def swapF {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ pullback (pullback.fst p ι ≫ p) U.hom :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition, pullback.condition]))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])

private def swapB {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.fst p ι ≫ p) U.hom ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by
      rw [pullback.lift_snd_assoc, ← pullback.condition, Category.assoc, pullback.condition])

private def swapI {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd p U.hom ≫ U.hom) ι ≅ pullback (pullback.fst p ι ≫ p) U.hom where
  hom := swapF p ι U
  inv := swapB p ι U
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

private def baseI {B : Scheme.{0}} (U : B.Etale) : U.left ≅ pullback (𝟙 B) U.hom where
  hom := pullback.lift U.hom (𝟙 _) (by simp)
  inv := pullback.snd _ _
  hom_inv_id := by simp [pullback.lift_snd]
  inv_hom_id := by
    apply pullback.hom_ext
    · have h := pullback.condition (f := 𝟙 B) (g := U.hom)
      simp only [Category.comp_id] at h
      simpa using h.symm
    · simp [pullback.lift_snd]

theorem UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange :
    ∀ {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B), Nonempty (gYW p ι ≅ gY (pullback.fst p ι ≫ p)) ∧ Nonempty (gB B ≅ gY (𝟙 B)) ∧ Nonempty (gBW ι ≅ gY ι) := by
  intro B Y W p ι
  refine ⟨⟨NatIso.ofComponents (fun U => swapI p ι U) ?_⟩,
    ⟨NatIso.ofComponents (fun U => baseI U) ?_⟩,
    ⟨NatIso.ofComponents (fun U => pullbackSymmetry U.hom ι) ?_⟩⟩
  · intro U U' a
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [swapI, swapF, gYW, gY, resY, resYW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapI, swapF, gYW, gY, resY, resYW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro U U' a
    have hw : a.left ≫ U'.hom = U.hom := by simpa using a.w
    apply pullback.hom_ext <;> simp [baseI, gB, gY, resY, pullback.map, hw, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro U U' a
    apply pullback.hom_ext <;>
      simp [gBW, gY, resY, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SectionsSpecPiBijectiveProdSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private noncomputable abbrev sι {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))

private lemma sι_eq {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    sι C i = Sigma.ι (fun i => Spec (CommRingCat.of (C i))) i ≫ sigmaSpec (fun i => CommRingCat.of (C i)) :=
  (ι_sigmaSpec (fun i => CommRingCat.of (C i)) i).symm

private theorem bijective_sheaf_sigma_restrict {P : Scheme.{0}ᵒᵖ ⥤ Type 1}
    (hP : Presieve.IsSheaf Scheme.zariskiTopology P) {n : ℕ} (X : Fin n → Scheme.{0}) :
    Function.Bijective (fun (s : P.obj (op (∐ X))) (i : Fin n) => P.map (Sigma.ι X i).op s) := by
  have hcov := hP.isSheafFor _ (sigmaOpenCover X).mem_grothendieckTopology
  rw [Presieve.isSheafFor_arrows_iff] at hcov
  have hcomp : ∀ x : ∀ i, P.obj (op (X i)), Presieve.Arrows.Compatible P (Sigma.ι X) x := by
    intro x i j Z gi gj h
    by_cases hij : i = j
    · subst hij
      rw [cancel_mono] at h
      rw [h]
    · haveI := isEmpty_of_commSq_sigmaι_of_ne ⟨h⟩ hij
      exact (hP (⊥ : Sieve Z) (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext
        (fun _ _ hf => hf.elim)
  constructor
  · intro s t hst
    exact (hcov (fun i => P.map (Sigma.ι X i).op s) (hcomp _)).unique (fun i => rfl)
      (fun i => (congr_fun hst i).symm)
  · intro y
    obtain ⟨t, ht, -⟩ := hcov y (hcomp y)
    exact ⟨t, funext ht⟩

theorem UpperTheory.sections_specPi_bijective_prod_sections :
    ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℕ) (C : Fin n → Type) [∀ i, CommRing (C i)],
        Function.Bijective (fun (s : Sec F (Spec (CommRingCat.of (∀ i, C i)))) (i : Fin n) =>
          (Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))) s : Sec F (Spec (CommRingCat.of (C i))))) := by
  intro R _ F n C _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology
      (F.obj ⋙ CategoryTheory.forget (ModuleCat (ULift.{1, 0} R))) := by
    apply Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)).mp F.property
  have key := bijective_sheaf_sigma_restrict hG (fun i => Spec (CommRingCat.of (C i)))
  have hiso : Function.Bijective ((F.obj ⋙ CategoryTheory.forget _).map
      (sigmaSpec (fun i => CommRingCat.of (C i))).op) :=
    (isIso_iff_bijective _).mp inferInstance
  convert key.comp hiso using 1
  funext s i
  rw [show Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) = _ from sι_eq C i]
  simp only [Sec.res, Function.comp_apply, op_comp, Functor.map_comp]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SmoothOfNormalCurvePerfectField
section
open IsLocalRing AlgebraicGeometry CategoryTheory

namespace UpperTheory.LocallyOfRingHomAway

private theorem exists_away (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    [Algebra Ω R] [Algebra.FiniteType Ω R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) (m : Ideal R) [hm : m.IsMaximal] :
    ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) := by
  have hnoeth : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Ω R
  have hkd : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff]
    exact_mod_cast hdim
  have hdl : Ring.DimensionLEOne R :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have hded : IsDedekindDomain R := { }
  have hmbot : m ≠ ⊥ := by
    intro h
    apply hnf
    rw [Ring.isField_iff_maximal_bot]
    rw [← h]
    exact hm
  let S := Localization.AtPrime m
  have hdvr : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hmbot S
  have hreg : IsRegularLocalRing S := inferInstance
  have hsm : Algebra.FormallySmooth Ω S :=
    GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField Ω S
  have het : Algebra.FormallyEtale Ω (ResidueField S) :=
    GlobalTheory.formallyEtale_residueField_of_isMaximal Ω Ω m S
  obtain ⟨_, hrk⟩ := GlobalTheory.free_and_finrank_kaehler_eq_finrank_cotangentSpace Ω S
  have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
    have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace S).mp hreg
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one S] at h1
    exact_mod_cast h1
  have hfp : Algebra.FinitePresentation Ω R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hsa : Algebra.IsSmoothAt Ω m := hsm
  exact GlobalTheory.exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt Ω m (hrk.trans hcot)

private theorem locally_of_ringHom (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    (ψ : Ω →+* R) (hft : ψ.FiniteType) (hic : IsIntegrallyClosed R)
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) ψ := by
  letI : Algebra Ω R := ψ.toAlgebra
  haveI : Algebra.FiniteType Ω R := hft
  refine ⟨{t | RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap R (Localization.Away t)).comp ψ)}, ?_, fun t ht => ht⟩
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, hsm⟩ := exists_away Ω R hdim hnf M
  apply hf
  apply hle
  apply Ideal.subset_span
  have heq : ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra =
      (inferInstance : Algebra Ω (Localization.Away f)) :=
    Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply Ω R _ r).symm)
  show @Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) _ _
    ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra
  rw [heq]
  exact hsm

end UpperTheory.LocallyOfRingHomAway

theorem UpperTheory.smooth_of_normal_curve_perfectField :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hint hlft hic hdim
  have key : ∀ (V : C.Opens) (hV : IsAffineOpen V) (a b : C), a ∈ V → b ∈ V → a ≠ b →
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
        (c.appLE ⊤ V (by simp)).hom := by
    intro V hV a b ha hb hab
    haveI : Nonempty V := ⟨⟨a, ha⟩⟩
    have hdom : IsDomain Γ(C, V) := inferInstance
    let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
    let ψ : Ω →+* Γ(C, V) := (c.appLE ⊤ V (by simp)).hom.comp ι.symm.toRingHom
    have hφ : (c.appLE ⊤ V (by simp)).hom = ψ.comp ι.toRingHom := by
      ext r
      simp [ψ]
    rw [hφ]
    apply (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).right
    apply UpperTheory.LocallyOfRingHomAway.locally_of_ringHom Ω Γ(C, V) ψ
    · have hft : (c.appLE ⊤ V (by simp)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType c hlft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact hft.comp (RingHom.FiniteType.of_surjective _ ι.symm.surjective)
    · refine IsIntegrallyClosed.of_localization_maximal (fun p _ hp => ?_)
      let y : PrimeSpectrum Γ(C, V) := ⟨p, hp.isPrime⟩
      have hy : hV.fromSpec y ∈ V := by
        have : hV.fromSpec y ∈ Set.range hV.fromSpec := ⟨y, rfl⟩
        rwa [hV.range_fromSpec] at this
      letI := TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨hV.fromSpec y, hy⟩
      haveI hloc : IsLocalization p.primeCompl (C.presheaf.stalk (hV.fromSpec y)) :=
        hV.isLocalization_stalk' y hy
      exact (hic (hV.fromSpec y)).of_equiv
        (IsLocalization.algEquiv p.primeCompl (C.presheaf.stalk (hV.fromSpec y))
          (Localization.AtPrime p)).toRingEquiv
    · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C, V)]
      change topologicalKrullDim (Spec Γ(C, V)) ≤ 1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le C V).trans hdim.le
    · intro hf
      letI := hf.toField
      have ha' : a ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact ha
      have hb' : b ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hb
      obtain ⟨pa, rfl⟩ := ha'
      obtain ⟨pb, rfl⟩ := hb'
      have hss : Subsingleton (PrimeSpectrum Γ(C, V)) := inferInstance
      exact hab (congrArg _ (hss.elim pa pb))
  have hgen : ∀ (W : C.Opens) (z : C), z ∈ W → genericPoint C ∈ W := by
    intro W z hz
    exact ((genericPoint_spec C).mem_open_set_iff W.isOpen).mpr ⟨z, trivial, hz⟩
  have hexists : ∃ z : C, z ≠ genericPoint C := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton (TopologicalSpace.IrreducibleCloseds C) := by
      refine ⟨fun s t => ?_⟩
      obtain ⟨p, hp⟩ := s.isIrreducible.nonempty
      obtain ⟨q, hq⟩ := t.isIrreducible.nonempty
      ext y
      rw [h y]
      exact ⟨fun _ => h q ▸ hq, fun _ => h p ▸ hp⟩
    have h0 := Order.krullDim_nonpos_of_subsingleton (α := TopologicalSpace.IrreducibleCloseds C)
    unfold topologicalKrullDim at hdim
    rw [hdim] at h0
    exact absurd h0 (by norm_num)
  rw [HasRingHomProperty.iff_exists_appLE (P := @SmoothOfRelativeDimension 1)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).left)]
  intro x
  by_cases hx : x = genericPoint C
  · obtain ⟨z, hz⟩ := hexists
    obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hx ▸ hgen W z hzW, by simp, ?_⟩
    exact key W hW z (genericPoint C) hzW (hgen W z hzW) hz
  · obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hxW, by simp, ?_⟩
    exact key W hW x (genericPoint C) hxW (hgen W x hxW) hx
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSuppOfSectionsV
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish :
    ∀ (Q : Scheme.{0} → Prop) (G : Shv ℤ), (∀ U : Scheme.{0}, Q U → Subsingleton (Sec G U)) → ∀ P : PSh, Supp Q P → ∀ n : ℤ, Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) G n) := by
  intro Q G hG P hP n
  apply UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology
  haveI : (res ℤ G).IsKInjective := (_root_.GlobalTheory.EtC.ResBasic.res_basic ℤ G).1
  refine GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support ℤ (disc.obj P) (res ℤ G) ?_ n
  intro U hU m b hb
  have hQ : Q U := hP U hU
  haveI : Subsingleton (Sec G U) := hG U hQ
  obtain ⟨h0, -, h3, hneg⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ G U
  have hz : ∀ (c : Sec ((res ℤ G).X m) U), b = c → c = 0 →
      Loc U fun V g => ∃ a : Sec ((res ℤ G).X (m - 1)) V,
        Sec.map ((res ℤ G).d (m - 1) m) a = Sec.res g b := by
    rintro c rfl rfl
    refine ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => ⟨0, ?_⟩⟩
    simp
  rcases lt_trichotomy m 0 with h | h | h
  · haveI := hneg m h
    exact hz b rfl (Subsingleton.elim _ _)
  · subst h
    obtain ⟨a, rfl⟩ := (h0 b).1 hb
    refine hz _ rfl ?_
    rw [Subsingleton.elim a 0]
    simp
  · exact h3 (m - 1) m (m + 1) h (by omega) b rfl hb
end

