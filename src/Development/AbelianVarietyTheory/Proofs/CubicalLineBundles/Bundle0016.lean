module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.DedekindExt

variable {X X' Y S : Scheme.{0}}

def Agree (φ : X' ⟶ X) (f : X' ⟶ Y) {W : Scheme.{0}} (i : W ⟶ X) (g : W ⟶ Y) : Prop :=
  ∀ (T : Scheme.{0}) (u : T ⟶ W) (u' : T ⟶ X'), u ≫ i = u' ≫ φ → u ≫ g = u' ≫ f

theorem Agree.comp {φ : X' ⟶ X} {f : X' ⟶ Y} {W W' : Scheme.{0}} {i : W ⟶ X} {g : W ⟶ Y}
    (h : Agree φ f i g) (c : W' ⟶ W) : Agree φ f (c ≫ i) (c ≫ g) := fun T u u' e => by
  rw [← Category.assoc]
  exact h T _ _ (by rw [Category.assoc, e])

theorem Agree.of_dominant {φ : X' ⟶ X} [Flat φ] {f : X' ⟶ Y} (sX : X ⟶ S) (sY : Y ⟶ S) [IsSeparated sY]
    (hf : f ≫ sY = φ ≫ sX) {W W' : Scheme.{0}} {i : W ⟶ X} {g : W ⟶ Y} (hg : g ≫ sY = i ≫ sX)
    (c : W' ⟶ W) [QuasiCompact c] [IsSchemeTheoreticallyDominant c] (h : Agree φ f (c ≫ i) (c ≫ g)) :
    Agree φ f i g := by
  have key : pullback.fst i φ ≫ g = pullback.snd i φ ≫ f := by
    have : IsSchemeTheoreticallyDominant (pullback.snd c (pullback.fst i φ)) :=
      .of_isPullback (IsPullback.of_hasPullback c (pullback.fst i φ))
    refine ExtUnique.hom_ext_of_dominant sY ?_ (pullback.snd c (pullback.fst i φ)) ?_
    · rw [Category.assoc, Category.assoc, hg, hf, pullback.condition_assoc]
    · rw [← pullback.condition_assoc, ← Category.assoc (pullback.snd _ _)]
      refine h _ _ _ ?_
      rw [pullback.condition_assoc, Category.assoc, pullback.condition]
  intro T u u' e
  rw [← pullback.lift_fst u u' e, Category.assoc, key, pullback.lift_snd_assoc]

theorem exists_open_agree [IsLocallyNoetherian X] {φ : X' ⟶ X} [Flat φ] {f : X' ⟶ Y} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsSeparated sY] [LocallyOfFiniteType sY] (hf : f ≫ sY = φ ≫ sX) (x : X)
    (g : Spec (X.presheaf.stalk x) ⟶ Y) (hg : g ≫ sY = X.fromSpecStalk x ≫ sX)
    (h : Agree φ f (X.fromSpecStalk x) g) :
    ∃ (W : Scheme.{0}) (i : W ⟶ X) (_ : IsOpenImmersion i) (g' : W ⟶ Y),
      x ∈ Set.range i ∧ g' ≫ sY = i ≫ sX ∧ Agree φ f i g' := by
  obtain ⟨U, hxU, g₁, h₁, h₂⟩ := spread_out_of_isGermInjective' sX sY g hg
  obtain ⟨V, hxV, hV, hVU, hinj⟩ := X.exists_le_and_germ_injective x U hxU
  have hr : Set.range hV.fromSpec ⊆ Set.range U.ι := by
    rw [hV.range_fromSpec, Scheme.Opens.range_ι]; exact hVU
  let l := IsOpenImmersion.lift U.ι hV.fromSpec hr
  have hl : l ≫ U.ι = hV.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have hc : Spec.map (X.presheaf.germ V x hxV) ≫ hV.fromSpec = X.fromSpecStalk x :=
    hV.fromSpecStalk_eq_fromSpecStalk hxV
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hinj
  have hg' : (l ≫ g₁) ≫ sY = hV.fromSpec ≫ sX := by rw [Category.assoc, h₂, ← Category.assoc, hl]
  refine ⟨_, hV.fromSpec, inferInstance, l ≫ g₁, by rw [hV.range_fromSpec]; exact hxV, hg',
    Agree.of_dominant sX sY hf hg' (Spec.map (X.presheaf.germ V x hxV)) ?_⟩
  have e : Spec.map (X.presheaf.germ V x hxV) ≫ l = U.fromSpecStalkOfMem x hxU := by
    rw [← cancel_mono U.ι, Category.assoc, hl, hc, Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [hc, ← Category.assoc, e, ← h₁]
  exact h

theorem exists_of_locally {U : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {φ : X' ⟶ X} {p : X' ⟶ U} {f : X' ⟶ Y} (sX : X ⟶ S) [Flat sX] (sY : Y ⟶ S) [IsSeparated sY]
    (hp : IsPullback φ p sX j)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (i : W ⟶ X) (_ : IsOpenImmersion i) (g' : W ⟶ Y),
      x ∈ Set.range i ∧ g' ≫ sY = i ≫ sX ∧ Agree φ f i g') :
    ∃ F : X ⟶ Y, F ≫ sY = sX ∧ φ ≫ F = f := by
  choose W i hι g hx hg ha using h
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X W i (fun x => ⟨x, hx x⟩)
  have : QuasiCompact φ := MorphismProperty.of_isPullback hp.flip ‹_›
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hp.flip
  have hc : ∀ x y, pullback.fst (i x) (i y) ≫ g x = pullback.snd (i x) (i y) ≫ g y := by
    intro x y
    let q := pullback.fst (i x) (i y) ≫ i x
    have : IsSchemeTheoreticallyDominant (pullback.fst q φ) :=
      .of_isPullback (IsPullback.of_hasPullback q φ).flip
    refine ExtUnique.hom_ext_of_dominant sY ?_ (pullback.fst q φ) ?_
    · rw [Category.assoc, Category.assoc, hg, hg, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine (ha x _ _ (pullback.snd q φ) ?_).trans (ha y _ _ (pullback.snd q φ) ?_).symm
      · rw [Category.assoc]; exact pullback.condition
      · rw [Category.assoc, ← pullback.condition]; exact pullback.condition
  have hF : ∀ x, i x ≫ 𝒰.glueMorphisms g hc = g x := fun x => 𝒰.ι_glueMorphisms g hc x
  refine ⟨𝒰.glueMorphisms g hc, 𝒰.hom_ext _ _ fun x : X => ?_,
    Scheme.Cover.hom_ext (𝒰.pullback₁ φ) _ _ fun x : X => ?_⟩
  · change i x ≫ _ = i x ≫ _
    rw [← Category.assoc, hF, hg]
  · change pullback.fst φ (i x) ≫ _ = pullback.fst φ (i x) ≫ _
    rw [pullback.condition_assoc, hF]
    exact ha x _ _ _ pullback.condition.symm

theorem exists_of_stalks [IsLocallyNoetherian X] {U : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [Flat j]
    [IsSchemeTheoreticallyDominant j]
    {φ : X' ⟶ X} {p : X' ⟶ U} {f : X' ⟶ Y} (sX : X ⟶ S) [Flat sX] (sY : Y ⟶ S) [IsSeparated sY]
    [LocallyOfFiniteType sY] (hp : IsPullback φ p sX j) (hf : f ≫ sY = φ ≫ sX)
    (h : ∀ s : S, ∃ (T : Scheme.{0}) (t : T ⟶ S) (a : Spec (S.presheaf.stalk s) ⟶ T) (g : pullback sX t ⟶ Y),
      a ≫ t = S.fromSpecStalk s ∧ g ≫ sY = pullback.fst sX t ≫ sX ∧ Agree φ f (pullback.fst sX t) g) :
    ∃ F : X ⟶ Y, F ≫ sY = sX ∧ φ ≫ F = f := by
  have : Flat φ := MorphismProperty.of_isPullback hp.flip ‹_›
  refine exists_of_locally sX sY hp fun x => ?_
  obtain ⟨T, t, a, g, ha, hg, hA⟩ := h (sX x)
  have e : X.fromSpecStalk x ≫ sX = (Spec.map (sX.stalkMap x) ≫ a) ≫ t := by
    rw [Category.assoc, ha, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h₁ := hA.comp (pullback.lift _ _ e)
  rw [pullback.lift_fst] at h₁
  exact exists_open_agree sX sY hf x _ (by rw [Category.assoc, hg, pullback.lift_fst_assoc]) h₁

theorem exists_spec_factor (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (M : Submonoid R)
    [IsLocalization M T] {A : CommRingCat.{0}} (ψ : CommRingCat.of R ⟶ A) (hu : ∀ y : M, IsUnit (ψ.hom y)) :
    ∃ a : Spec A ⟶ Sp T, a ≫ spMap (algebraMap R T) = Spec.map ψ := by
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (S := T) hu)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact IsLocalization.lift_eq hu r

theorem exists_fromSpecStalk_factor (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (M : Submonoid R)
    [IsLocalization M T] (s : PrimeSpectrum R) (hM : M ≤ s.asIdeal.primeCompl) :
    ∃ a : Spec ((Sp R).presheaf.stalk s) ⟶ Sp T, a ≫ spMap (algebraMap R T) = (Sp R).fromSpecStalk s := by
  have hu : ∀ y : M, IsUnit ((StructureSheaf.toStalk R s).hom y) := fun y =>
    IsLocalization.map_units ((Spec.structureSheaf R).presheaf.stalk s) (⟨y.1, hM y.2⟩ : s.asIdeal.primeCompl)
  obtain ⟨a, ha⟩ := exists_spec_factor R T M (StructureSheaf.toStalk R s) hu
  exact ⟨a, ha.trans (Spec.fromSpecStalk_eq' (CommRingCat.of R) s).symm⟩

theorem exists_agree_of_extend {U T : Scheme.{0}} {k : U ⟶ T} {t : T ⟶ S} [Mono t] {j : U ⟶ S} (hj : k ≫ t = j)
    (G G' : Over S) [GrpObj G] [GrpObj G'] (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (h : ∀ f' : (Over.pullback k).obj ((Over.pullback t).obj G) ⟶ (Over.pullback k).obj ((Over.pullback t).obj G'),
      IsMonHom f' → ∃ F, (Over.pullback k).map F = f') :
    ∃ g : pullback G.hom t ⟶ G'.left, g ≫ G'.hom = pullback.fst G.hom t ≫ G.hom ∧
      Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst G'.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j)
    (((isGrpPullback_pullback _ k).comp (isGrpPullback_pullback G t)).congr hj rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback G' j)
    (((isGrpPullback_pullback _ k).comp (isGrpPullback_pullback G' t)).congr hj rfl)
  obtain ⟨F, hF⟩ := h (a.inv ≫ f ≫ b.hom) inferInstance
  have hF' : (a.hom ≫ (Over.pullback k).map F).left = (f ≫ b.hom).left := by rw [hF, a.hom_inv_id_assoc]
  have hw : F.left ≫ pullback.snd G'.hom t = pullback.snd G.hom t := Over.w F
  have hw' : a.hom.left ≫ pullback.snd ((Over.pullback t).obj G).hom k = pullback.snd G.hom j := Over.w a.hom
  refine ⟨F.left ≫ pullback.fst G'.hom t, ?_, fun Z u u' e => ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  · have key : (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) ≫ F.left ≫ pullback.fst G'.hom t =
        f.left ≫ pullback.fst G'.hom j := by
      have h₁ := ExtUnique.pullback_map_left_fst k F
      rw [Over.comp_left, Over.comp_left] at hF'
      rw [← hb', ← reassoc_of% hF', reassoc_of% h₁]
      exact Category.assoc _ _ _
    have hfst : (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) ≫ pullback.fst G.hom t =
        pullback.fst G.hom j := (Category.assoc _ _ _).trans ha'
    have hu : u = u' ≫ (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) := by
      have : Mono (pullback.fst G.hom t) := inferInstance
      rw [← cancel_mono (pullback.fst G.hom t), e]
      exact (congrArg (u' ≫ ·) hfst.symm).trans (Category.assoc _ _ _).symm
    rw [hu]
    exact (Category.assoc _ _ _).trans (congrArg (u' ≫ ·) key)

end GlobalTheory.DedekindExt

namespace GlobalTheory

open DedekindExt

theorem abelianScheme_hom_extends_dedekind :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f := by
  intro H R K _ _ _ _ _ G G' _ _ hG hG' f hf
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG'.proper
  have : IsPreimmersion (spMap (algebraMap R K)) := .of_isLocalization (nonZeroDivisors R)
  have : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have hw : f.left ≫ pullback.snd G'.hom _ = pullback.snd G.hom _ := Over.w f
  have hf₀ : (f.left ≫ pullback.fst G'.hom _) ≫ G'.hom = pullback.fst G.hom _ ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  obtain ⟨F, hF, hF'⟩ := exists_of_stalks G.hom G'.hom (IsPullback.of_hasPullback G.hom (spMap (algebraMap R K)))
    hf₀ fun s : PrimeSpectrum R => by
      by_cases hs : s.asIdeal = ⊥
      · obtain ⟨a, ha⟩ := exists_fromSpecStalk_factor R K (nonZeroDivisors R) s fun r hr hr' =>
          nonZeroDivisors.ne_zero hr (by simpa [hs] using hr')
        refine ⟨_, _, a, _, ha, hf₀, fun Z u u' e => ?_⟩
        rw [(cancel_mono _).1 e]
      · let T := Localization.AtPrime s.asIdeal
        have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hs T
        letI : Algebra T K := IsLocalization.localizationAlgebraOfSubmonoidLe T K s.asIdeal.primeCompl
          (nonZeroDivisors R) s.asIdeal.primeCompl_le_nonZeroDivisors
        have : IsScalarTower R T K := IsLocalization.localization_isScalarTower_of_submonoid_le T K _ _ _
        have : IsFractionRing T K :=
          IsFractionRing.isFractionRing_of_isDomain_of_isLocalization s.asIdeal.primeCompl T K
        have : IsPreimmersion (spMap (algebraMap R T)) := .of_isLocalization s.asIdeal.primeCompl
        obtain ⟨a, ha⟩ := exists_fromSpecStalk_factor R T s.asIdeal.primeCompl s le_rfl
        have hj : spMap (algebraMap T K) ≫ spMap (algebraMap R T) = spMap (algebraMap R K) := by
          rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R T K]; rfl
        obtain ⟨g, hg, hA⟩ := exists_agree_of_extend hj G G' f fun f' hf' => by
          obtain ⟨F, hF, -⟩ := H T K _ _
            (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ G hG))
            (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ G' hG')) f' hf'
          exact ⟨F, hF.2⟩
        exact ⟨_, _, a, g, ha, hg, hA⟩
  have e : (Over.pullback (spMap (algebraMap R K))).map (Over.homMk F hF : G ⟶ G') = f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (ExtUnique.pullback_map_left_fst _ _).trans hF'
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨Over.homMk F hF, ⟨ExtUnique.isMonHom_of_pullback _ _ (e ▸ hf), e⟩, fun F' hF'' => ?_⟩
  exact ExtUnique.pullback_map_injective _ G G' (hF''.2.trans e.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorLieBasisExists
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct
open GlobalTheory.GrpTangent

namespace GlobalTheory.SerreLie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff (c : R) (v x : epsR R ⟶ G) :
    IsLieComb ![c] ![v] x ↔ x = GrpTangent.epsScale c ≫ v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u 0 = GrpTangent.epsScale c ≫ v := Over.OverMorphism.ext (hu 0)
    simp [h]
  · rintro rfl
    refine ⟨![GrpTangent.epsScale c ≫ v], fun i => ?_, by simp⟩
    fin_cases i
    rfl

variable [IsCommMonObj G] {O : Type} [CommRing O] [Algebra O R]

def multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) : R →ₗ[O] Pts a (epsR R) where
  toFun r := Pts.mk a (GrpTangent.epsScale r ≫ v)
  map_add' r s := Pts.ext (epsScale_add_comp r s hv)
  map_smul' c r := Pts.ext (by
    simp only [Pts.hom_mk, RingHom.id_apply, Pts.hom_smul, Category.assoc, ha]
    rw [epsScale_mul_assoc, Algebra.smul_def, mul_comm])

theorem hom_multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) (r : R) :
    (multiples a hv ha r).hom = GrpTangent.epsScale r ≫ v := rfl

omit [Algebra O R] in
theorem pre_eq_zero_iff (a : OAct O G) (x : Pts a (epsR R)) :
    Pts.pre a (toUnit (epsR R) ≫ epsZero R) x = 0 ↔ IsTangent x.hom := by
  rw [isTangent_iff]
  constructor
  · intro h
    have h1 : (toUnit (epsR R) ≫ epsZero R) ≫ x.hom = 1 := congrArg Pts.hom h
    have h2 := congrArg (epsZero R ≫ ·) h1
    simp only [← Category.assoc, MonObj.comp_one] at h2
    rwa [toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.id_comp] at h2
  · intro h
    exact Pts.ext (by rw [Pts.hom_pre, Category.assoc, h, MonObj.comp_one]; rfl)

omit [Algebra O R] in
theorem isTangent_sub_pre (a : OAct O G) (x : Pts a (epsR R)) :
    IsTangent (x - Pts.pre a (toUnit (epsR R) ≫ epsZero R) x).hom := by
  rw [← pre_eq_zero_iff, map_sub, sub_eq_zero]
  apply Pts.ext
  simp only [Pts.hom_pre, ← Category.assoc]
  rw [Category.assoc (toUnit _) (epsZero R) (toUnit _),
    toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.comp_id]

theorem exists_retraction (a : OAct O G) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) :
    ∃ ρ : Pts a (epsR R) →ₗ[O] R, ρ ∘ₗ multiples a (hv.1 0) ha = LinearMap.id ∧
      multiples a (hv.1 0) ha ∘ₗ ρ = LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) := by
  have hinj : Function.Injective (multiples a (hv.1 0) ha) := fun r s h => by
    have h' : GrpTangent.epsScale r ≫ v = GrpTangent.epsScale s ≫ v := congrArg Pts.hom h
    have := (hv.2 _ (isTangent_epsScale r (hv.1 0))).unique
      ((isLieComb_one_iff r v _).2 rfl) ((isLieComb_one_iff s v _).2 h')
    exact congrFun this 0
  have hsur : ∀ x : Pts a (epsR R), ∃ r, multiples a (hv.1 0) ha r =
      (LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) : _ →ₗ[O] _) x := fun x => by
    obtain ⟨c, hc, -⟩ := hv.2 _ (isTangent_sub_pre a x)
    have e : c = ![c 0] := by ext i; fin_cases i; rfl
    rw [e, isLieComb_one_iff] at hc
    exact ⟨c 0, Pts.ext hc.symm⟩
  choose ρ hρ using hsur
  refine ⟨⟨⟨ρ, fun x y => hinj ?_⟩, fun c x => hinj ?_⟩, LinearMap.ext fun r => hinj ?_,
    LinearMap.ext hρ⟩
  · rw [map_add (f := _), hρ, hρ, hρ, map_add (f := _)]
  · simp only [RingHom.id_apply, map_smul, hρ]
  · change multiples a (hv.1 0) ha (ρ _) = _
    rw [hρ, LinearMap.sub_apply, (pre_eq_zero_iff a (multiples a (hv.1 0) ha r)).2
      (isTangent_epsScale r (hv.1 0)), sub_zero]
    rfl

theorem exists_lie_tensor : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] [Algebra O R] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (v : epsR R ⟶ G), IsLieBasis ![v] → (∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) → ∃ Φ : R ⊗[O] M → (epsR R ⟶ A), Function.Injective Φ ∧ (∀ x, IsTangent x ↔ x ∈ Set.range Φ) ∧ (∀ y z, Φ (y + z) = Φ y * Φ z) ∧ (∀ (c : R) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) ∧ (∀ m, Φ (1 ⊗ₜ m) = v ≫ t.tmul m) ∧ ∀ (φ : M →ₗ[O] M) y, Φ (φ.baseChange R y) = Φ y ≫ t.mapLeft t φ := by
  intro R _ G _ _ O _ _ M _ _ _ _ A _ _ a b t v hv ha'
  have ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v :=
    fun c => (isLieComb_one_iff _ _ _).1 (ha' c)
  obtain ⟨ρ, h₁, h₂⟩ := exists_retraction a hv ha
  set j := multiples a (hv.1 0) ha with hj
  let Ψ : R ⊗[O] M →ₗ[O] Pts b (epsR R) :=
    (t.equiv _).toLinearMap ∘ₗ j.lTensor M ∘ₗ (TensorProduct.comm O R M).toLinearMap
  have hΨ : ∀ (r : R) (m : M), (Ψ (r ⊗ₜ m)).hom = GrpTangent.epsScale r ≫ v ≫ t.tmul m := fun r m => by
    simp [Ψ, hj, hom_multiples]
  refine ⟨fun y => (Ψ y).hom, fun y z h => ?_, fun x => ⟨fun hx => ?_, ?_⟩, fun y z => ?_,
    fun c y => ?_, fun m => ?_, fun φ y => ?_⟩
  · have h' : j.lTensor M (TensorProduct.comm O R M y) = j.lTensor M (TensorProduct.comm O R M z) :=
      (t.equiv _).injective (Pts.ext h)
    have h'' := congrArg (ρ.lTensor M) h'
    simp only [← LinearMap.lTensor_comp_apply, h₁, LinearMap.lTensor_id, LinearMap.id_apply] at h''
    exact (TensorProduct.comm O R M).injective h''
  · obtain ⟨z, hz⟩ := (t.equiv (epsR R)).surjective (Pts.mk b x)
    have h0 : (Pts.pre a (toUnit (epsR R) ≫ epsZero R)).lTensor M z = 0 := by
      apply (t.equiv _).injective
      rw [t.natural, hz, map_zero]
      exact (pre_eq_zero_iff b _).2 hx
    refine ⟨(TensorProduct.comm O R M).symm (ρ.lTensor M z), ?_⟩
    simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← LinearMap.lTensor_comp_apply, h₂, LinearMap.lTensor_sub, LinearMap.sub_apply, h0,
      sub_zero, LinearMap.lTensor_id, LinearMap.id_apply, hz, Pts.hom_mk]
  · rintro ⟨y, rfl⟩
    rw [← pre_eq_zero_iff]
    induction y with
    | tmul r m =>
      rw [pre_eq_zero_iff, hΨ]
      exact isTangent_epsScale r (isTangent_comp (hv.1 0) _)
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
  · simp only [map_add (f := _), Pts.hom_add]
  · rw [isLieComb_one_iff]
    induction y with
    | tmul r m =>
      simp only [TensorProduct.smul_tmul', hΨ, smul_eq_mul]
      rw [epsScale_mul_assoc]
    | add y z hy hz =>
      simp only [smul_add, map_add (f := _), Pts.hom_add, MonObj.comp_mul] at hy hz ⊢
      rw [hy, hz]
  · simp only [hΨ, epsScale_one, Category.id_comp]
  · induction y with
    | tmul r m => simp only [LinearMap.baseChange_tmul, hΨ, Category.assoc, IsTensor.tmul_mapLeft]
    | add y z hy hz =>
      simp only [map_add (f := _), Pts.hom_add, MonObj.mul_comp] at hy hz ⊢
      rw [hy, hz]

end GlobalTheory.SerreLie
end
end

