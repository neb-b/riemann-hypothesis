module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorNontrivial
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section Factor

open GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_tau_four (D : DegPre R) (a b : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val t r z J = val (D.tau a b) r z J := by
  refine exists_gen D.P.isLB ?_ (D.tau a b) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _))) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  intro U _ h
  have e : toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, lamPts, negε, ← e]
  simp [eSec, Hom.one_def]

end Factor
end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.GenericFibreChart

theorem isPullback_of_fac_mono {C : Type*} [Category C] {P V G S T : C} {p : P ⟶ G} {q : P ⟶ T}
    {h : G ⟶ S} {j : T ⟶ S} (H : IsPullback p q h j) (i : V ⟶ G) [Mono i] (l : P ⟶ V)
    (hl : l ≫ i = p) : IsPullback l q (i ≫ h) j := by
  have w : l ≫ i ≫ h = q ≫ j := by rw [← Category.assoc, hl, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift (s.fst ≫ i) s.snd (by rw [Category.assoc]; exact s.condition)) ?_ ?_ ?_⟩⟩
  · intro s
    rw [← cancel_mono i, Category.assoc, hl, H.lift_fst]
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, ← h1, Category.assoc, hl]
    · rw [H.lift_snd, h2]

theorem isPullback_of_comp_mono {C : Type*} [Category C] {P X Y W Z : C} {p : P ⟶ X} {q : P ⟶ Y}
    {a : X ⟶ W} {g : Y ⟶ W} (m : W ⟶ Z) [Mono m] (H : IsPullback p q (a ≫ m) (g ≫ m)) :
    IsPullback p q a g := by
  have w : p ≫ a = q ≫ g := by
    rw [← cancel_mono m, Category.assoc, Category.assoc, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift s.fst s.snd (by
      rw [← Category.assoc, ← Category.assoc, s.condition])) ?_ ?_ ?_⟩⟩
  · intro s
    exact H.lift_fst _ _ _
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, h1]
    · rw [H.lift_snd, h2]

theorem exists_isPullback_generic :
    ∀ (R₀ : Type) [CommRing R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) (R : Type)
      [CommRing R] [IsDomain R] (ρ : R₀ →+* R), ρ f ≠ 0 →
      ∀ (G : Over (Sp R)) (V : G.left.Opens) (φ : V.toScheme ⟶ A.left),
      (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) →
      IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ GlobalTheory.Desc.awayMap f) (spMap ρ) →
      ∃ (g : Sp (FractionRing R) ⟶ Sp (Localization.Away f))
        (l : pullback G.hom (jK R) ⟶ V.toScheme),
        l ≫ V.ι = pullback.fst G.hom (jK R) ∧
          IsPullback (l ≫ φ) (pullback.snd G.hom (jK R)) A.hom g := by
  intro R₀ _ f A R _ _ ρ hf G V φ hV hP
  have hu : IsUnit (((algebraMap R (FractionRing R)).comp ρ) f) := by
    rw [isUnit_iff_ne_zero, RingHom.comp_apply]
    exact fun h => hf ((IsFractionRing.injective R (FractionRing R)) (by rw [h, map_zero]))
  let ψ : Localization.Away f →+* FractionRing R := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R₀ (Localization.Away f)) =
      (algebraMap R (FractionRing R)).comp ρ := IsLocalization.Away.lift_comp f hu
  have hg : spMap ψ ≫ GlobalTheory.Desc.awayMap f = jK R ≫ spMap ρ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
  have hr : Set.range (pullback.fst G.hom (jK R)) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (hV _).2 ?_
    have hx : G.hom (pullback.fst G.hom (jK R) x) = jK R (pullback.snd G.hom (jK R) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [hx]
    intro hmem
    have hmem' : algebraMap R (FractionRing R) (ρ f) ∈
        (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).asIdeal := hmem
    exact (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem' hu)
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  refine ⟨spMap ψ, IsOpenImmersion.lift V.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have h1 := isPullback_of_fac_mono (IsPullback.of_hasPullback G.hom (jK R)) V.ι
    (IsOpenImmersion.lift V.ι _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h2 := h1.paste_horiz hP
  refine isPullback_of_comp_mono (GlobalTheory.Desc.awayMap f) ?_
  rw [hg]
  exact h2

end GlobalTheory.GenericFibreChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoPreimageBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartPart

theorem flat_preimage_of_stalk {R Rc : Type} [CommRing R] [CommRing Rc] [IsLocalRing Rc] (ξ : Sp Rc ⟶ Sp R)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) : (Spec.preimage ξ).hom.Flat := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of Rc) ξ
  have h2 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := HasRingHomProperty.Spec_iff.mpr h
  have h3 : Flat ξ := by
    rw [← h1]
    exact MorphismProperty.comp_mem @Flat _ _ h2 (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  rw [← Spec.map_preimage ξ] at h3
  exact HasRingHomProperty.Spec_iff.mp h3

theorem injective_of_flat {R Rc : Type} [CommRing R] [IsDomain R] [CommRing Rc] [Nontrivial Rc] (ρ : R →+* Rc)
    (h : ρ.Flat) : Function.Injective ρ := by
  algebraize [ρ]
  exact FaithfulSMul.algebraMap_injective R Rc

theorem isPullback_away {R Rc : Type} [CommRing R] [CommRing Rc] (ρ : R →+* Rc) (f : R) :
    IsPullback (spMap (Localization.awayMap ρ f)) (spMap (algebraMap Rc (Localization.Away (ρ f)))) (awayMap f)
      (spMap ρ) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_)
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    simp [Localization.awayMap, IsLocalization.Away.map]
  · rw [Scheme.Hom.opensRange_localizationAway (R := .of R), Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
    rfl

theorem exists_iso_preimage_basicOpen {Rc : Type} [CommRing Rc] (G : Over (Sp Rc)) (r : Rc) :
    ∃ e : (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ≅
      pullback G.hom (spMap (algebraMap Rc (Localization.Away r))),
      e.hom ≫ pullback.fst _ _ = (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι := by
  refine ⟨IsOpenImmersion.isoOfRangeEq _ (pullback.fst _ _) ?_, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
  simp

theorem exists_pff_of_flat {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (hV : (V : Set Y).Nonempty)
    (φ : V.toScheme ⟶ X) [Flat φ] : ∃ θ : X.functionField →+* Y.functionField, PFF V.ι φ θ := by
  have hη : genericPoint Y ∈ V := ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hrange : Set.range (gp Y) ⊆ Set.range V.ι := by
    rw [gp, Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun y hy => hy.mem_open V.isOpen hη
  let l := IsOpenImmersion.lift V.ι (gp Y) hrange
  have hl : l ≫ V.ι = gp Y := IsOpenImmersion.lift_fac _ _ _
  have hl0 : V.ι (l (closedPoint Y.functionField)) = genericPoint Y := by
    have : (l ≫ V.ι) (closedPoint Y.functionField) = genericPoint Y := by
      rw [hl]; exact Scheme.fromSpecStalk_closedPoint
    exact this
  have hx : (l ≫ φ) (closedPoint Y.functionField) = genericPoint X := by
    obtain ⟨v, hv, hφv⟩ := Flat.generalizingMap φ
      (genericPoint_specializes (φ (l (closedPoint Y.functionField))))
    have h1 : V.ι v ⤳ genericPoint Y := hl0 ▸ hv.map V.ι.continuous
    have h2 : V.ι v = genericPoint Y := (h1.antisymm (genericPoint_specializes _)).eq
    have h3 : v = l (closedPoint Y.functionField) := V.ι.isOpenEmbedding.injective (h2.trans hl0.symm)
    subst h3
    exact hφv
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := Y.functionField) (l ≫ φ)
  revert hφ
  generalize Scheme.stalkClosedPointTo (R := Y.functionField) (l ≫ φ) = ψ
  revert ψ
  rw [show (l ≫ φ) (closedPoint Y.functionField) = genericPoint X from hx]
  intro ψ hψ
  exact ⟨ψ.hom, l, hl, hψ.symm⟩

end GlobalTheory.Desc.ChartPart

namespace GlobalTheory.Desc


open GlobalTheory.Desc.ChartPart in
theorem chart_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ [IsIntegral A.left] (x : Sp R) (C : Chart (awayMap f) A x) [IsIntegral C.G.left], ∃ (ρ : R →+* C.R) (V : C.G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* C.G.left.functionField), C.ξ = spMap ρ ∧ ρ.Flat ∧ (∀ z : C.G.left, z ∈ V ↔ ρ f ∉ (C.G.hom z).asIdeal) ∧ IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) ∧ (∀ (T : Scheme.{0}) (t : T ⟶ pullback C.G.hom (jK C.R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ C.α = t' ≫ φ) ∧ PFF V.ι φ θ := by
  intro R _ _ _ f hf0 A _ hAb _ x C _
  set ρ : R →+* C.R := (Spec.preimage C.ξ).hom with hρdef
  have hξ : C.ξ = spMap ρ := by
    rw [hρdef]; exact (Spec.map_preimage C.ξ).symm
  have hflat : ρ.Flat := flat_preimage_of_stalk C.ξ C.etc.1
  have hρf : ρ f ≠ 0 := fun h => hf0 (injective_of_flat ρ hflat (h.trans (map_zero ρ).symm))
  obtain ⟨_, hnorm⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R

  let Rf := Localization.Away (ρ f)
  have hle : Submonoid.powers (ρ f) ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors hρf
  haveI : IsDomain Rf := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers (ρ f)) Rf inferInstance
  haveI : IsIntegrallyClosed Rf := isIntegrallyClosed_of_isLocalization Rf _ hle
  let ιf : C.R →+* Rf := algebraMap C.R Rf
  let g : Sp Rf ⟶ Sp (Localization.Away f) := spMap (Localization.awayMap ρ f)
  have sq2 := isPullback_away ρ f

  let K := FractionRing C.R
  have hu : IsUnit (algebraMap C.R K (ρ f)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R K)).mpr hρf)
  letI : Algebra Rf K := (Localization.awayLift (algebraMap C.R K) (ρ f) hu).toAlgebra
  haveI : IsScalarTower C.R Rf K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap C.R K r = Localization.awayLift (algebraMap C.R K) (ρ f) hu (algebraMap C.R Rf r)
    exact (IsLocalization.Away.lift_eq (ρ f) hu r).symm
  haveI : IsFractionRing Rf K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (ρ f)) Rf K
  let j : Sp K ⟶ Sp Rf := spMap (algebraMap Rf K)
  have hjK : j ≫ spMap ιf = jK C.R := by
    simp only [j, spMap, ← Spec.map_comp]; congr 1; ext r
    exact (IsScalarTower.algebraMap_apply C.R Rf K r).symm
  have hy' : j ≫ g = C.y := by
    rw [← cancel_mono (awayMap f), Category.assoc, sq2.w, ← Category.assoc, hjK, C.hy, hξ]

  let GK := (Over.pullback (jK C.R)).obj C.G
  letI : GrpObj GK := Functor.grpObjObj
  let G₁ := (Over.pullback (spMap ιf)).obj C.G
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback (spMap ιf) C.G C.semi
  let H₁ := (Over.pullback g).obj A
  letI : GrpObj H₁ := Functor.grpObjObj
  have hH₁ : IsSemiAbelian H₁ :=
    IsSemiAbelian.pullback g A (isSemiAbelian_of_isAbelianScheme A hAb)
  let i₁ : GK.left ⟶ G₁.left := pullback.lift (pullback.fst C.G.hom (jK C.R)) (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hjK]; exact pullback.condition)
  have h₁ : IsGrpPullback GK G₁ j i₁ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback C.G (spMap ιf)) ?_ (pullback.lift_snd _ _ _)
    exact (isGrpPullback_pullback C.G (jK C.R)).congr hjK.symm (pullback.lift_fst _ _ _).symm
  let i₂ : GK.left ⟶ H₁.left := pullback.lift C.α (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hy']; exact C.gen.1.w)
  have h₂ : IsGrpPullback GK H₁ j i₂ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback A g) ?_ (pullback.lift_snd _ _ _)
    exact C.gen.congr hy'.symm (pullback.lift_fst _ _ _).symm
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsGenericPointHom.fractionField Rf K) hG₁ hH₁ h₁ h₂

  haveI : IsMonHom E.hom := hEm
  let φ₁ : G₁.left ⟶ A.left := E.hom.left ≫ pullback.fst A.hom g
  have sq1 : IsPullback φ₁ G₁.hom A.hom g :=
    (((isGrpPullback_of_iso E).comp (isGrpPullback_pullback A g)).congr (Category.id_comp g) rfl).1

  let V : C.G.left.Opens := C.G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ρ f)
  obtain ⟨e, he⟩ := exists_iso_preimage_basicOpen C.G (ρ f)
  let φ : V.toScheme ⟶ A.left := e.hom ≫ φ₁
  have sq0 : IsPullback e.hom (V.ι ≫ C.G.hom) (G₁.hom ≫ spMap ιf) (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    show e.hom ≫ pullback.snd _ _ ≫ spMap ιf = (V.ι ≫ C.G.hom) ≫ 𝟙 _
    rw [Category.comp_id, ← pullback.condition, ← Category.assoc, he]
  have hcart : IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) := by
    have := sq0.paste_horiz (sq1.paste_vert sq2)
    rwa [Category.id_comp] at this
  haveI : Flat (spMap ρ) := HasRingHomProperty.Spec_iff.mpr hflat
  haveI : Flat φ := MorphismProperty.of_isPullback hcart.flip inferInstance

  have hVne : (V : Set C.G.left).Nonempty := by
    let s : Sp C.R ⟶ C.G.left := (η[C.G] : 𝟙_ (Over (Sp C.R)) ⟶ C.G).left
    have hs : s ≫ C.G.hom = 𝟙 _ := Over.w η[C.G]
    let p : Sp C.R := (⊥ : PrimeSpectrum C.R)
    refine ⟨s p, ?_⟩
    show ρ f ∉ (C.G.hom (s p)).asIdeal
    rw [← Scheme.Hom.comp_apply, hs]
    exact fun h => hρf (Ideal.mem_bot.1 h)
  obtain ⟨θ, hθ⟩ := exists_pff_of_flat V hVne φ
  refine ⟨ρ, V, φ, θ, hξ, hflat, fun z => Iff.rfl, hcart, ?_, hθ⟩
  intro T t t' htt'
  have key : t ≫ i₁ = t' ≫ e.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, htt', Category.assoc, he]
    · rw [← cancel_mono (spMap ιf)]
      have l : t ≫ i₁ ≫ pullback.snd _ _ ≫ spMap ιf = t ≫ pullback.fst _ _ ≫ C.G.hom := by
        simp only [i₁, pullback.lift_snd_assoc, Category.assoc, hjK]; rw [pullback.condition]
      have r : t' ≫ e.hom ≫ pullback.snd _ _ ≫ spMap ιf = t' ≫ V.ι ≫ C.G.hom := by
        rw [← pullback.condition, ← Category.assoc e.hom, he]
      simp only [Category.assoc]
      rw [l, r, ← Category.assoc t, htt', Category.assoc]
  have : t ≫ C.α = t ≫ i₂ ≫ pullback.fst A.hom g := by rw [pullback.lift_fst]
  rw [this, ← hE, Category.assoc, ← Category.assoc t, key, Category.assoc]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelActionTripleOverlap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem pullTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    pullTop (f ≫ g) u = pullTop f (pullTop g u) := by
  ext
  simp only [pullTop, Units.coe_map, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

section Tri

variable {S : Scheme.{0}} (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A)

def triM₁₂ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _) (lift (snd A _ ≫ fst N _) (snd A _ ≫ snd N _ ≫ snd N T))

def triM₂₃ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _ * (snd A _ ≫ fst N _ ≫ i)) (snd A _ ≫ snd N (N ⊗ T))

def triM₁₃ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _) (lift (snd A _ ≫ fst N _ * (snd A _ ≫ snd N _ ≫ fst N T)) (snd A _ ≫ snd N _ ≫ snd N T))

theorem triM₁₂_actMap_eq : triM₁₂ A N T ≫ actMap i T = triM₂₃ A N T i ≫ prMap A N T := by
  apply hom_ext <;> simp [triM₁₂, triM₂₃, actMap, prMap, comp_mul]

theorem tri_isPullback_over : IsPullback (triM₁₂ A N T) (triM₂₃ A N T i) (actMap i T) (prMap A N T) := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (triM₁₂_actMap_eq A N T i))
    (PullbackCone.IsLimit.mk (triM₁₂_actMap_eq A N T i)
      (fun s => lift (s.fst ≫ fst A _) (lift (s.fst ≫ snd A _ ≫ fst N T)
        (lift (s.snd ≫ snd A _ ≫ fst N T) (s.fst ≫ snd A _ ≫ snd N T)))) ?_ ?_ ?_)
  · intro s
    apply hom_ext
    · simp [triM₁₂]
    · apply hom_ext <;> simp [triM₁₂]
  · intro s
    have h := s.condition
    have h₁ := congrArg (· ≫ fst A T) h
    have h₂ := congrArg (· ≫ snd A T) h
    simp only [Category.assoc, actMap, prMap, lift_fst, lift_snd, comp_mul] at h₁ h₂
    apply hom_ext
    · simp [triM₂₃, comp_mul, ← h₁]
    · apply hom_ext
      · simp [triM₂₃]
      · simp [triM₂₃, h₂]
  · intro s m h₁ h₂
    have e₁ := congrArg (· ≫ fst A _) h₁
    have e₂ := congrArg (· ≫ snd A _ ≫ fst N T) h₁
    have e₃ := congrArg (· ≫ snd A _ ≫ snd N T) h₁
    have e₄ := congrArg (· ≫ snd A _ ≫ fst N T) h₂
    simp only [triM₁₂, triM₂₃, Category.assoc, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e₁ e₂ e₃ e₄
    apply hom_ext
    · simpa using e₁
    · apply hom_ext
      · simpa using e₂
      · apply hom_ext
        · simpa using e₄
        · simpa using e₃

theorem triM₁₃_prMap : triM₁₃ A N T ≫ prMap A N T = triM₁₂ A N T ≫ prMap A N T := by
  apply hom_ext <;> simp [triM₁₃, triM₁₂, prMap]

theorem triM₁₃_actMap [IsMonHom i] : triM₁₃ A N T ≫ actMap i T = triM₂₃ A N T i ≫ actMap i T := by
  apply hom_ext
  · simp only [triM₁₃, triM₂₃, actMap, comp_lift, lift_fst, lift_fst_assoc, lift_snd_assoc, comp_mul, mul_comp,
      Category.assoc]
    exact (mul_assoc _ _ _).symm
  · simp [triM₁₃, triM₂₃, actMap]

theorem triM₁₃_snd : triM₁₃ A N T ≫ snd A (N ⊗ T) =
    snd A (N ⊗ (N ⊗ T)) ≫ lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T) := by
  apply hom_ext <;> simp [triM₁₃, comp_mul]

theorem triM₁₂_snd : triM₁₂ A N T ≫ snd A (N ⊗ T) =
    snd A (N ⊗ (N ⊗ T)) ≫ lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T) := by
  apply hom_ext <;> simp [triM₁₂]

theorem triM₂₃_snd : triM₂₃ A N T i ≫ snd A (N ⊗ T) = snd A (N ⊗ (N ⊗ T)) ≫ snd N (N ⊗ T) := by
  simp [triM₂₃]

end Tri

theorem triOverlap : ∀ (S : Scheme.{0}) (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A) (χ : Γ((N ⊗ T).left, ⊤)ˣ),
    IsMonHom i → IsCharacter χ → ∃ (W : Scheme.{0}) (m₁₂ m₂₃ m₁₃ : W ⟶ (A ⊗ (N ⊗ T)).left),
      IsPullback m₁₂ m₂₃ (actMap i T).left (prMap A N T).left ∧
      m₁₃ ≫ (prMap A N T).left = m₁₂ ≫ (prMap A N T).left ∧
      m₁₃ ≫ (actMap i T).left = m₂₃ ≫ (actMap i T).left ∧
      pullTop m₁₃ (pullTop (snd A (N ⊗ T)).left χ) =
        pullTop m₁₂ (pullTop (snd A (N ⊗ T)).left χ) * pullTop m₂₃ (pullTop (snd A (N ⊗ T)).left χ) := by
  intro S A N T _ _ i χ hi hχ
  haveI := hi
  refine ⟨(A ⊗ (N ⊗ (N ⊗ T))).left, (triM₁₂ A N T).left, (triM₂₃ A N T i).left, (triM₁₃ A N T).left,
    (tri_isPullback_over A N T i).map (Over.forget S), ?_, ?_, ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, triM₁₃_prMap]
  · rw [← Over.comp_left, ← Over.comp_left, triM₁₃_actMap]
  · rw [← pullTop_comp_apply, ← pullTop_comp_apply, ← pullTop_comp_apply, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
      triM₁₃_snd, triM₁₂_snd, triM₂₃_snd, Over.comp_left, Over.comp_left, Over.comp_left, pullTop_comp_apply, pullTop_comp_apply,
      pullTop_comp_apply]
    unfold IsCharacter at hχ
    rw [hχ, map_mul]

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreementLocusOfAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.GlueKernel

theorem same_comp {S : Scheme.{0}} {A U T Y Y' : Over S} {M : LB (A ⊗ U).left} {N : LB (A ⊗ T).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T) (h : Same A M N u t) :
    Same A M N (f ≫ u) (f ≫ t) := by
  rw [same_iff hM hN] at h ⊢
  have e := congrArg (GlobalTheory.CechPic.pull (A ◁ f).left) h
  rw [pull_evc, pull_evc] at e
  simpa only [whiskerLeft_fst, whiskerLeft_snd_assoc] using e

theorem exists_kernel_of_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → (∀ V : T.left.affineOpens, ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), Same A M N u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), Same A M N u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  intro R _ _ A _ hA U T M N hM hN h0M h0N hV
  exact _root_.GlobalTheory.exists_closedImmersion_represents_of_affineOpens (Sp R) U T (fun Y u t => Same A M N u t)
    (fun Y Y' f u t h => same_comp hM hN f u t h)
    (fun Y u t h => _root_.GlobalTheory.DualCon.SameLocal.same_of_local R A hA U T M N hM hN h0M h0N Y u t h) hV

end GlobalTheory.DualCon.GlueKernel
end

