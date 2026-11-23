module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefDescent

theorem exists_algebraic_point : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧ (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) :=
  GlobalTheory.T.exists_mem_fiber_isAlgebraic_residueField_of_lft

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) :=
  GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue

theorem exists_curve_over : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F),
    π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    topologicalKrullDim (Z : Set X) = 1 → ∃ C : Closeds Y, IsIrreducible (C : Set Y) ∧
      topologicalKrullDim (C : Set Y) = 1 ∧ π '' (C : Set Y) = (Z : Set X) := by
  intro F _ Y X π sX p hπ hX hY hs Z hZi hZd
  obtain ⟨hPX, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  subst hπ
  have : IsProper π := IsProper.of_comp π sX
  obtain ⟨η, hη⟩ := QuasiSober.sober hZi Z.isClosed
  obtain ⟨y₀, hy₀⟩ := π.surjective η
  obtain ⟨y, hy, halg⟩ := exists_algebraic_point Y X π y₀
  have hd := dim_closure_eq_of_isAlgebraic F Y X π sX y halg
  rw [hy, hy₀, hη.def] at hd
  refine ⟨Closeds.closure {y}, isIrreducible_singleton.closure, ?_, ?_⟩
  · exact hd.trans hZd
  · change π '' closure {y} = Z
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hy, hy₀, hη.def]

theorem isNef_of_pull : ∀ (F : Type) [Field F] [NumberField F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F) (L : LB X) (hL : L.IsLB) (L' : LB Y) (hL' : L'.IsLB), π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → CechPic.pull π (cls L hL) = cls L' hL' → (letI := algebraΓOfHom p; IsNef F L') → (letI := algebraΓOfHom sX; IsNef F L) := by
  intro F _ _ Y X π sX p L hL L' hL' hπ hX hY hs hcl hnef
  letI := algebraΓOfHom sX
  letI := algebraΓOfHom p
  have hnef' : IsNef F L' := hnef
  obtain ⟨hPX, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, A', hA'⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  have : IsProper (strHom F (X := X)) := by rwa [strHom_eq (f := sX) fun _ => rfl]
  have : IsProper (strHom F (X := Y)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  refine ⟨hL, fun Z hZ => ?_⟩
  obtain ⟨C, hCi, hCd, hCZ⟩ := exists_curve_over F Y X π sX p hπ hX hY hs Z hZ.1 hZ.2
  have hC : IsCompleteCurve F C := (isCompleteCurve_iff (f := p) (fun _ => rfl)).2 ⟨hCi, hCd⟩
  by_contra hneg
  push_neg at hneg
  have hM := isLB_dual hL
  have hMpos : 0 < interNumRed F Z ![dual L] := by rw [hZ.interNumRed_dual hA hL]; linarith
  obtain ⟨r, hr, s, hs0⟩ := PosBaseChange.exists_hasNonzeroSec (k := F) hA hM hZ.1 hZ.2.le fun _ => hMpos
  have hr' := isLB_lbPow hM r
  have hZc : Closeds.closure (π '' (C : Set Y)) = Z := by
    ext1
    simp only [Closeds.coe_closure, hCZ, Z.isClosed.closure_eq]
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ π := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ π) (by
    rw [← hZc, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩
  have hsφ : Function.Surjective φ := fun z => by
    obtain ⟨y, hy, e⟩ := hCZ.ge ((range_redι Z).le ⟨z, rfl⟩)
    obtain ⟨y, rfl⟩ := (range_redι C).ge hy
    exact ⟨y, (redι Z).isClosedEmbedding.injective ((congrArg (fun q => q y) hφ).trans e)⟩
  have := isIntegral_red hC.1
  have := isIntegral_red hZ.1

  obtain ⟨z, hz⟩ : ∃ z, z ∉ nonzeroLocus s := by
    by_contra! h
    obtain ⟨t, ht⟩ := exists_isGen_of_nonzeroLocus_eq_top s (top_unique fun z _ => h z)
    have e0 := (cls_eq_zero_iff (LB.isLB_pull hr' (redι Z))).2 ⟨t, ht⟩
    have h1 : interNumRed F Z ![lbPow (dual L) r] = 0 := by
      letI := algebraΓAlong F (redι Z)
      rw [interNumRed_one_eq hr']
      exact interNum_eq_zero_of_cls_eq_zero F _ (isLB_vecOne (LB.isLB_pull hr' _)) 0 e0
    rw [hZ.interNumRed_lbPow hA hM] at h1
    have : (0 : ℤ) < r := by exact_mod_cast hr
    nlinarith
  letI := algebraΓAlong F (redι C)
  have := hC.isProper_strHom
  obtain ⟨x, hx⟩ := hsφ (genericPoint _)
  have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge (by
    change φ x ∈ nonzeroLocus s
    rw [hx]; exact (sec_ne_zero_iff s).1 hs0)
  obtain ⟨c, hc⟩ := hsφ z
  have h0 := (interNum_one_nonneg_of_sec (k := F) (hA'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hCd) (LB.isLB_pull (LB.isLB_pull hr' _) φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).2 (fun htop => hz (by
        have := (nonzeroLocus_secPull s φ).le (htop.ge (show c ∈ (⊤ : Opens _) from trivial))
        rw [← hc]; exact this))
  have hD' := isLB_dual hL'
  have hP' := isLB_lbPow hD' r
  have h1 : interNumRed F C ![lbPow (dual L') r] =
      interNum F (structureModule _) ![((lbPow (dual L) r).pull (redι Z)).pull φ] := by
    rw [interNumRed_one_eq hP']
    refine interNum_congr_cls F _ (isLB_vecOne (LB.isLB_pull hP' _))
      (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hr' _) φ)) fun i => ?_
    fin_cases i
    change pull (redι C) (cls _ hP') = pull φ (pull (redι Z) (cls _ hr'))
    rw [← pull_comp, hφ, pull_comp, cls_lbPow hD', cls_lbPow hM, cls_dual hL', cls_dual hL, ← hcl]
    simp only [map_nsmul, map_neg]
  rw [← h1, hC.interNumRed_lbPow hA' hD', hC.interNumRed_dual hA' hL'] at h0
  have h2 := hnef'.2 C hC
  have : (0 : ℤ) ≤ r := by positivity
  nlinarith

end GlobalTheory.NefDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem isPullback_whiskerLeft_snd_left {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) :
    IsPullback (A ◁ j).left (snd A B').left (snd A B).left j.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst A.hom B.hom) (v₁₃ := A.hom) (h₂₂ := B.hom)
    ?_ ?_ (IsPullback.of_hasPullback A.hom B.hom)
  · have hw : j.left ≫ B.hom = B'.hom := Over.w j
    rw [Over.whiskerLeft_left_fst, hw]
    exact IsPullback.of_hasPullback A.hom B'.hom
  · simp

theorem isOpenImmersion_whiskerLeft_left_and_range {S : Scheme.{0}} (A : Over S) {B' B : Over S}
    (j : B' ⟶ B) [IsOpenImmersion j.left] :
    IsOpenImmersion (A ◁ j).left ∧
      Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  have h := isPullback_whiskerLeft_snd_left A j
  refine ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) h.flip
    inferInstance, ?_⟩
  simpa [Set.image_univ] using Scheme.image_preimage_eq_of_isPullback h.flip Set.univ

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem baseIdeal_comp_eq_comap (R : Type) [CommRing R] (J : Ideal R) {W T : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) :
    baseIdeal (i ≫ f) J = (baseIdeal f J).comap i := by
  set m := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  obtain ⟨h0c, h0k, -⟩ := _root_.GlobalTheory.FormalAlg.baseChange_quotient R J W _ f (pullback.fst f m) (pullback.snd f m)
    (IsPullback.of_hasPullback f m)
  obtain ⟨-, h1k, -⟩ := _root_.GlobalTheory.FormalAlg.baseChange_quotient R J T _ (i ≫ f) (pullback.fst (i ≫ f) m) (pullback.snd (i ≫ f) m)
    (IsPullback.of_hasPullback (i ≫ f) m)
  haveI := h0c
  rw [← h1k, ← h0k, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← pullbackRightPullbackFstIso_hom_fst f m i, Scheme.Hom.ker_comp_of_isIso]

theorem map_baseIdeal_comp (R : Type) [CommRing R] (J : Ideal R) {W T : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (hi : IsClosedImmersion i) :
    (baseIdeal (i ≫ f) J).map i = i.ker ⊔ baseIdeal f J := by
  have h := (_root_.GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map T W i hi ⊥ (baseIdeal f J)).1
  rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h
  rw [baseIdeal_comp_eq_comap, h]

theorem reduces_iff_ker_eq : ∀ (R : Type) [CommRing R] (J : Ideal R) (W T Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (j : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsClosedImmersion i → IsClosedImmersion j → j ≫ f = q ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ((∃ b : Y ⟶ T, b ≫ i = j ∧ IsPullback b q (i ≫ f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ↔ i.ker ⊔ baseIdeal f J = j.ker) := by
  intro R _ J W T Y f i j q hi hj hq
  haveI := hi
  haveI := hj
  constructor
  · rintro ⟨b, hb, hpb⟩
    obtain ⟨-, hbk, -⟩ := _root_.GlobalTheory.FormalAlg.baseChange_quotient R J T Y (i ≫ f) b q hpb
    rw [← hb, Scheme.Hom.ker_comp, hbk, map_baseIdeal_comp R J f i hi]
  · intro hk
    set m := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    obtain ⟨h1c, h1k, -⟩ := _root_.GlobalTheory.FormalAlg.baseChange_quotient R J T _ (i ≫ f) (pullback.fst (i ≫ f) m)
      (pullback.snd (i ≫ f) m) (IsPullback.of_hasPullback (i ≫ f) m)
    haveI := h1c
    have hker : (pullback.fst (i ≫ f) m ≫ i).ker = j.ker := by
      rw [Scheme.Hom.ker_comp, h1k, map_baseIdeal_comp R J f i hi, hk]
    let e := IsClosedImmersion.lift (pullback.fst (i ≫ f) m ≫ i) j hker.le
    have he : e ≫ pullback.fst (i ≫ f) m ≫ i = j := IsClosedImmersion.lift_fac _ _ _
    haveI : IsIso e := IsClosedImmersion.isIso_of_ker_eq j _ e he hker.symm
    haveI : IsClosedImmersion m := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono m := inferInstance
    have hqe : e ≫ pullback.snd (i ≫ f) m = q := by
      rw [← cancel_mono m, ← hq, Category.assoc, ← pullback.condition, ← he]
      simp only [Category.assoc]
    refine ⟨e ≫ pullback.fst (i ≫ f) m, by rw [Category.assoc, he], ?_⟩
    rw [← hqe]
    exact IsPullback.of_iso (IsPullback.of_hasPullback (i ≫ f) m) (asIso e).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingLocalizationOfComapEqBot
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericFibreFactorial

theorem isRegularRing_localization_of_comap_eq_bot (R A : Type) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] (p : Ideal A) [p.IsPrime]
    (hp : p.comap (algebraMap R A) = ⊥) : IsRegularRing (Localization.AtPrime p) := by
  let K := FractionRing R
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  let B := Localization M
  letI : Algebra K B := localizationAlgebra (nonZeroDivisors R) A
  haveI : IsScalarTower R K B := inferInstance
  haveI h1 : Algebra.IsPushout R A K B :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors R) K A B
  haveI : Algebra.IsPushout R K A B := h1.symm
  haveI : Algebra.Smooth K B := Algebra.Smooth.of_equiv (Algebra.IsPushout.equiv (R := R) (S := K) (R' := A) (S' := B))
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_smooth K B
  have disj : Disjoint (M : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrp
    have : r ∈ p.comap (algebraMap R A) := hrp
    rw [hp, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hr this
  let q := p.map (algebraMap A B)
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B p inferInstance disj
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
    exact (IsLocalization.under_map_of_isPrime_disjoint M B inferInstance disj).symm
  haveI : IsRegularRing (Localization.AtPrime q) :=
    GlobalTheory.ExtendRig.isRegularRing_of_isLocalization q.primeCompl _
  exact IsRegularRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

theorem ufd_stalk_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp R) [Smooth f] (x : X), (show PrimeSpectrum R from f x).asIdeal = ⊥ →
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  intro R _ _ X _ f _ x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  haveI : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨f x, trivial⟩⟩
  haveI : IsDomain Γ(Sp R, ⊤) := inferInstance
  have hgen : f x = genericPoint (Sp R) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hx
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) ⊤ (isAffineOpen_top _) U hU le_top hxU
  have h2 : (isAffineOpen_top (Sp R)).primeIdealOf ⟨f x, (show f x ∈ (⊤ : (Sp R).Opens) from trivial)⟩ =
      genericPoint (Spec Γ(Sp R, ⊤)) := by
    rw [← (isAffineOpen_top (Sp R)).primeIdealOf_genericPoint]
    congr 1
    exact Subtype.ext hgen
  rw [h2, genericPoint_eq_bot_of_affine] at h1
  have hcomap : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.comap (f.appLE ⊤ U le_top).hom = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h1
  algebraize [(f.appLE ⊤ U le_top).hom]
  have hreg := isRegularRing_localization_of_comap_eq_bot Γ(Sp R, ⊤) Γ(X, U)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal hcomap
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsRegularRing (X.presheaf.stalk x) :=
    IsRegularRing.of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
  exact GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _

end GlobalTheory.GenericFibreFactorial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJets
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ThetaOfJet

open GlobalTheory.MBLow.JetUniq

theorem isGenSec_of_polAVSectionInverseImage {K : Type} [Field K] (x : KeyIn K)
    (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
    (h : IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th) : IsGenSec x.P.A x.P.L 1 th := by
  have e : th = TrSec.thSec x.P x.th := by
    refine NormTheta.sec_ext fun j => ?_
    obtain ⟨i, rfl⟩ : ∃ i : x.P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact (h i (TrSec.chart_le x.P _)).trans (TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th i (TrSec.chart_le x.P _)).symm
  subst e
  haveI : Subsingleton (Over.mk (𝟙 (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine (GenSecFibre.isGenSec_iff_fibres firstFiveLaws.2.1 (Sp K) x.P K (𝟙 _) _).2 fun p => ?_
  obtain ⟨z, -, hz⟩ := x.th_ne p
  exact ⟨_, Subsingleton.elim _ _, TrSec.nonzero_thSec x.P x.th z hz⟩

theorem ptSecT_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (z : baseOver (Sp R) ⟶ A) :
    (ptSecT A z).left = z.left ≫ toProd A := by
  rw [toProd, ← Over.comp_left, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

open GlobalTheory.MBLow.JetUniq

theorem fnOf_valR_id {K : Type} [Field K] (f : Γ(Sp K, ⊤)) : GlobalTheory.Ex.fnOf (valR (𝟙 (Sp K)) ⊤ f) = f := by
  have h : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  rw [valR, dite_eq_left h]
  simp [GlobalTheory.Ex.fnOf, Scheme.Hom.appLE]
  rfl

theorem isThetaPt_of_thJet : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  intro K _ x g hg m hm hK I pt ϑ J hJ
  obtain ⟨th, hth, U, t, i₀, c, hUT, hi₀, H⟩ := hJ
  have hLaw : Laws := firstFiveLaws.1
  have hL := x.P.isLB
  let T : Over (Sp K) := baseOver (Sp K)
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ x.P m
  have e₁ : (snd T x.P.A).left ≫ (mulA x.P.A m).left = (snd T x.P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T x.P.A).left, (snd T x.P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen x.P.L ![𝟙 x.P.A.left, (mulA x.P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T x.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A T m) (snd T x.P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT x.P.A (U i).pt) (translPt x.P.A (U i).pt)
    (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) (U i).φ (U i).isGen s₁
  have ht : ∀ i, t i = s₂ i := fun i => NormTheta.sec_ext (tr_unique x.P x.rig hm (fun _ => rfl) (hUT i).1 (hUT i).1
    (hUT i).2 ⟨α, s₁, hα, hn, hs₁, hs₂ i⟩)
  let τ := rigT x.P.A x.P.L x.rig T ((m ^ 2 : ℕ) : ℤ)
  have hτ : τ.IsGen := NormTheta.rigT_isGen x.rig_gen _
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) 1 τ hτ
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := fun z hz => hi₀ hz
  let r : K := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  let V₁ := (x.P.L.LinComb (fun _ : Fin 1 => (1 : T ⟶ x.P.A).left) fun _ => ((m ^ 2 : ℕ) : ℤ)).U fun _ => i₀
  let q : K := valR (𝟙 (Sp K)) V₁ (τ.s fun _ => i₀).val
  have hq₀ : q ≠ 0 := (isUnit_valR (𝟙 (Sp K)) V₁ (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hp : (ptSecT x.P.A (1 : T ⟶ x.P.A)).left = eSec x.P.A ≫ toProd x.P.A := by
    rw [ptSecT_left, NormTheta.one_left]
    exact congrArg (· ≫ toProd x.P.A) (Category.id_comp _)
  let j₀ : Fin g := ⟨0, hg ▸ x.g_pos⟩
  have hval : ∀ i, valR (𝟙 (Sp K)) ⊤ (w i) * q = r ^ (m ^ 2) * ϑ i := fun i => by
    have e2 := GlobalTheory.ZH.TorsReg.valR_valueAt x.P.A x.P.L _ (hw i) (𝟙 (Sp K)) i₀ (by
      rintro _ ⟨z, rfl⟩; exact k₀ trivial)
    rw [Category.id_comp, hp, ← ht i] at e2
    let V := LB.wchart x.P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) x.P.A).left) fun _ => i₀
    have e : (valR (epsLift (x.v (Fin.cast hg.symm j₀))) V ((t i).f fun _ => i₀)).fst = r ^ (m ^ 2) * ϑ i := by
      have := congrArg TrivSqZeroExt.fst (H i j₀)
      simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr,
        add_zero] at this
      exact this
    rw [epsLift_eq] at e
    erw [GlobalTheory.HolHom.valR_comp (A := DualNumber K) (x.v (Fin.cast hg.symm j₀)).left (toProd x.P.A) V] at e
    rw [fst_valR (x.basis.1 _) (le_toProd k₀)] at e
    erw [← GlobalTheory.HolHom.valR_comp (A := K) (eSec x.P.A) (toProd x.P.A) V] at e
    exact e2.symm.trans e
  have un : ∀ a : K, a ≠ 0 → IsUnit (fnOf a) := fun a ha =>
    (IsUnit.mk0 _ ha).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hmu : IsUnit (m : Γ(T.left, ⊤)) := by
    have := un m hK
    rwa [GlobalTheory.Ex.fnOf, map_natCast] at this
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ThetaSeries.isThetaPt_of_data x.P hm hmu (Nat.cast_pow m 2) th s₁ α τ U s₂ w
    (un _ (div_ne_zero hq₀ (pow_ne_zero (m ^ 2) hr₀))).unit
    ⟨isGenSec_of_polAVSectionInverseImage x th hth, hα, hτ, hs₁, fun i => (hUT i).1, hs₂, hw, fun i => ?_⟩
  rw [IsUnit.unit_spec, ← fnOf_valR_id (w i), ← map_mul]
  congr 1
  field_simp
  linear_combination (hval i).symm

end GlobalTheory.MBLow.ThetaOfJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

open GlobalTheory.DeRham

variable {K : Type} [Field K]

def IsTransl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (w : Sp (DualNumber B) ⟶ A.left) : Prop :=
  ∃ x' v' : Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) ⟶ A,
    x'.left = spMap (algebraMap B (DualNumber B)) ≫ x ∧ v'.left = spMap (dualMap φ) ≫ v.left ∧ (x' * v').left = w

def IsCechKS (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) (L : LB A.left)
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι)
    (lam : ∀ (_ : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B], (Sp B ⟶ A.left) → (Sp B ⟶ A'.left)),
    ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧
    (∀ k (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) → ⊤ ≤ x ⁻¹ᵁ W k →
      lam k B x ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧
      spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ lam k B x =
        spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i ∧
      ∀ (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'),
        spMap (ρ : B →+* B') ≫ lam k B x = lam k B' (spMap (ρ : B →+* B') ≫ x)) ∧
    ∀ (k k' : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
      (O : A'.left.Opens) (f : Γ(A'.left, O)) (w : Fin n → (Sp (DualNumber B) ⟶ A.left)),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) →
      ⊤ ≤ x ⁻¹ᵁ (W k ⊓ W k') → ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O) →
      (∀ a, IsTransl ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) x (u a) (w a)) →
      valR (lam k B x) O f - valR (lam k' B x) O f =
        algebraMap (DualNumber K) B DualNumber.eps *
          ∑ a, ∑ b, (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K)) (θ a b) *
            ((valR (w b) _ (L.g (c k) (c k')).val).snd * valR x _ (L.g (c k) (c k'))⁻¹.val) *
            (valR (w a) (i ⁻¹ᵁ O) ((i.app O).hom f)).snd

end GlobalTheory.CechKS
end
end

