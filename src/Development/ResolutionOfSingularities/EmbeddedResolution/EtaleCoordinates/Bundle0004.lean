module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
public import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
section
universe u

namespace FunctorialResolution.EmbeddedResolution

@[reducible] def CoordPolynomialRing (k : Type u) [Field k] (m : ℕ) : Type u :=
  MvPolynomial (ULift.{u} (Fin m)) k

noncomputable def etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (j : Fin m) : S :=
  algebraMap (CoordPolynomialRing k m) S (MvPolynomial.X (ULift.up.{u} j))

theorem etaleChartCoord_def (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (j : Fin m) :
    etaleChartCoord k m S j =
      algebraMap (CoordPolynomialRing k m) S (MvPolynomial.X (ULift.up.{u} j)) :=
  rfl

private theorem isRegularLocalRing_localization_coordPolynomialRing (k : Type u) [Field k] (m : ℕ)
    (p : Ideal (CoordPolynomialRing k m)) (hp : p.IsPrime) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have := hp
  infer_instance

private theorem isRegularLocalRing_and_ringKrullDim_eq_of_etale (P S : Type u) [CommRing P] [CommRing S] [Algebra P S]
    [Algebra.Etale P S] [IsNoetherianRing P]
    (hreg : ∀ (p : Ideal P) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A ∧
      ringKrullDim A = ringKrullDim (Localization.AtPrime (q.comap (algebraMap P S))) := by
  have : Algebra.FiniteType P S := inferInstance
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing P S
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing q.primeCompl A inferInstance
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A q
  let : Algebra P A := ((algebraMap S A).comp (algebraMap P S)).toAlgebra
  have : IsScalarTower P S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat P S := inferInstance
  have : Module.Flat S A := IsLocalization.flat A q.primeCompl
  have : Module.Flat P A := Module.Flat.trans P S A
  have : Algebra.FormallyUnramified P S := inferInstance
  have : Algebra.FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  have : Algebra.FormallyUnramified P A := Algebra.FormallyUnramified.comp P S A
  have : Algebra.EssFiniteType P S := inferInstance
  have : Algebra.EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A q.primeCompl
  have : Algebra.EssFiniteType P A := Algebra.EssFiniteType.comp P S A
  have hunits : ∀ y : (q.comap (algebraMap P S)).primeCompl, IsUnit (algebraMap P A (y : P)) := by
    rintro ⟨y, hy⟩
    have hy' : algebraMap P S y ∈ q.primeCompl := hy
    have h := IsLocalization.map_units A ⟨algebraMap P S y, hy'⟩
    rw [IsScalarTower.algebraMap_apply P S A]
    exact h
  let : Algebra (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (IsLocalization.lift hunits).toAlgebra
  have : IsScalarTower P (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm
  have : Module.Flat (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.comap (algebraMap P S)))
      (q.comap (algebraMap P S)).primeCompl A).mpr ‹_›
  have : Algebra.FormallyUnramified (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.FormallyUnramified.localization_base (M := (q.comap (algebraMap P S)).primeCompl)
  have : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.EssFiniteType.of_comp P (Localization.AtPrime (q.comap (algebraMap P S))) A
  have : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap P S))) :=
    hreg _
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) := by
    constructor
    intro r hr
    obtain ⟨⟨x, s⟩, hx⟩ :=
      IsLocalization.surj (M := (q.comap (algebraMap P S)).primeCompl) r
    have hxA : algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A r
        * algebraMap P A (s : P) = algebraMap P A x := by
      have h := congrArg (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) hx
      rw [map_mul] at h
      rw [IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A (s : P),
        IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A x]
      exact h
    have h2 : IsUnit (algebraMap P A x) := by
      rw [← hxA]
      exact hr.mul (hunits s)
    have h3 : IsUnit (algebraMap S A (algebraMap P S x)) := by
      rw [← IsScalarTower.algebraMap_apply P S A]
      exact h2
    have h4 : algebraMap P S x ∈ q.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff A q (algebraMap P S x)).mp h3
    have h5 : x ∈ (q.comap (algebraMap P S)).primeCompl := h4
    have h6 : IsUnit (algebraMap P (Localization.AtPrime (q.comap (algebraMap P S))) x) :=
      IsLocalization.map_units _ ⟨x, h5⟩
    rw [← hx] at h6
    exact (IsUnit.mul_iff.mp h6).1
  exact ⟨isRegularLocalRing_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A,
    ringKrullDim_eq_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A⟩

theorem isRegularLocalRing_of_isLocalization_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A :=
  (isRegularLocalRing_and_ringKrullDim_eq_of_etale (CoordPolynomialRing k m) S
    (by intro p hp; exact isRegularLocalRing_localization_coordPolynomialRing k m p hp) q A).1

theorem isRegularLocalRing_localization_atPrime_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  isRegularLocalRing_of_isLocalization_etale k m S q (Localization.AtPrime q)

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsOpenImmersion
section
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def closedPreimage {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X) :
    TopologicalSpace.Closeds X' :=
  ⟨f.base ⁻¹' (S : Set X), S.isClosed.preimage f.continuous⟩

theorem closedPreimage_coe {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X) :
    (closedPreimage f S : Set X') = f.base ⁻¹' (S : Set X) := rfl

theorem reducedInverseImage_eq_vanishingIdeal_closedPreimage {X X' : Scheme.{u}} (f : X' ⟶ X)
    (S : TopologicalSpace.Closeds X) :
    reducedInverseImage f S = Scheme.IdealSheafData.vanishingIdeal (closedPreimage f S) := rfl

private theorem support_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

private theorem isRadical_map_of_bijective {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) {I : Ideal R} (hI : I.radical = I) :
    (Ideal.map φ I).radical = Ideal.map φ I := by
  refine le_antisymm ?_ Ideal.le_radical
  intro y hy
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hy
  obtain ⟨z, rfl⟩ := hφ.2 y
  rw [← map_pow] at hm
  obtain ⟨w, hw, hw2⟩ := (Ideal.mem_map_iff_of_surjective φ hφ.2).mp hm
  have hz : z ^ m ∈ I := by
    have hwz : w = z ^ m := hφ.1 hw2
    rwa [hwz] at hw
  have hzI : z ∈ I := by
    rw [← hI]
    exact Ideal.mem_radical_iff.mpr ⟨m, hz⟩
  exact Ideal.mem_map_of_mem _ hzI

private theorem ideal_eq_span_of_map_eq_span {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (ψ : S →+* R) (hψφ : ∀ r, ψ (φ r) = r) (I : Ideal R) (b : S)
    (hb : Ideal.map φ I = Ideal.span {b}) : I = Ideal.span {ψ b} := by
  have h2 : Ideal.map ψ (Ideal.map φ I) = I := by
    rw [Ideal.map_map, show ψ.comp φ = RingHom.id R from RingHom.ext hψφ, Ideal.map_id]
  rw [← h2, hb, Ideal.map_span, Set.image_singleton]

private theorem isRegularParameterSystem_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (v : Fin n → R) (w : Fin n → S)
    (hvw : ∀ i, e (v i) = w i) (hv : IsRegularParameterSystem R n v) :
    IsRegularParameterSystem S n w := by
  have h1 := hv.1
  have h2 := hv.2
  refine ⟨?_, ?_⟩
  · have hw : w = fun i => (e : R →+* S) (v i) := funext fun i => (hvw i).symm
    rw [hw, show (Set.range fun i => (e : R →+* S) (v i)) = (e : R →+* S) '' Set.range v from
      Set.range_comp _ _, ← Ideal.map_span, h1]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  · rw [h2]
    exact ringKrullDim_eq_of_ringEquiv e

private theorem isIso_appLE_image {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h] (U : X.Opens)
    (e : U ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ U)) :
    IsIso (h.appLE (h ''ᵁ U) U e) := by
  rw [show h.appLE (h ''ᵁ U) U e = (h.appIso U).hom from (Scheme.Hom.appIso_hom' h U).symm]
  infer_instance

private theorem stalkMap_germ_eq_germ_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ (TopologicalSpace.Opens.map f.base).obj U) (x : X) (hx : x ∈ V)
    (hfx : f.base x ∈ U) (s : Γ(Y, U)) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hfx s)
      = X.presheaf.germ V x hx (f.appLE U V e s) := by
  have key : Y.presheaf.germ U (f.base x) hfx ≫ f.stalkMap x
      = f.app U ≫ X.presheaf.germ ((TopologicalSpace.Opens.map f.base).obj U) x hfx := by
    simp
  have key2 : f.stalkMap x (Y.presheaf.germ U (f.base x) hfx s)
      = X.presheaf.germ ((TopologicalSpace.Opens.map f.base).obj U) x hfx (f.app U s) := by
    rw [← CommRingCat.comp_apply, key, CommRingCat.comp_apply]
  have h1 : f.appLE U V e s = X.presheaf.map (homOfLE e).op (f.app U s) := rfl
  rw [key2, h1, TopCat.Presheaf.germ_res_apply]

private theorem comap_ideal_radical_eq_of_isOpenImmersion {X' Y' : Scheme.{u}} (h : X' ⟶ Y') [IsOpenImmersion h]
    (I : Y'.IdealSheafData) (hI : I.radical = I) (V : X'.affineOpens) :
    ((I.comap h).ideal V).radical = (I.comap h).ideal V := by
  have hU : IsAffineOpen (h ''ᵁ V.1) := V.2.image_of_isOpenImmersion h
  have he : V.1 ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ V.1) :=
    le_of_eq (Scheme.Hom.preimage_image_eq h V.1).symm
  have : IsIso (h.appLE (h ''ᵁ V.1) V.1 he) := isIso_appLE_image h V.1 he
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨h ''ᵁ V.1, hU⟩ V he]
  refine isRadical_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (h.appLE (h ''ᵁ V.1) V.1 he)) ?_
  rw [← Scheme.IdealSheafData.radical_ideal, hI]

theorem comap_vanishingIdeal_of_isOpenImmersion {X' Y' : Scheme.{u}} (h : X' ⟶ Y')
    [IsOpenImmersion h] (Z : TopologicalSpace.Closeds Y') :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = Scheme.IdealSheafData.vanishingIdeal (closedPreimage h Z) := by
  have hZrad : (Scheme.IdealSheafData.vanishingIdeal Z).radical
      = Scheme.IdealSheafData.vanishingIdeal Z := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal]
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap h := by
    refine Scheme.IdealSheafData.ext (funext fun V => ?_)
    rw [Scheme.IdealSheafData.radical_ideal]
    exact comap_ideal_radical_eq_of_isOpenImmersion h _ hZrad V
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).support
      = closedPreimage h Z := by
    refine SetLike.ext fun x => ?_
    simp only [Scheme.IdealSheafData.mem_support_comap]
    exact Iff.rfl
  calc (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).support := by
        rw [Scheme.IdealSheafData.vanishingIdeal_support]
    _ = Scheme.IdealSheafData.vanishingIdeal (closedPreimage h Z) := by rw [hsupp]

theorem comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq {X' Y' : Scheme.{u}} (h : X' ⟶ Y')
    [IsOpenImmersion h] (Z : TopologicalSpace.Closeds Y') (Z' : TopologicalSpace.Closeds X')
    (hZ' : (Z' : Set X') = h.base ⁻¹' (Z : Set Y')) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = Scheme.IdealSheafData.vanishingIdeal Z' := by
  have h1 : closedPreimage h Z = Z' := SetLike.ext' (by rw [closedPreimage_coe, hZ'])
  rw [comap_vanishingIdeal_of_isOpenImmersion, h1]

theorem isStrictNormalCrossingsAt_base_of_comap {X' Y' : Scheme.{u}} (h : X' ⟶ Y') [IsOpenImmersion h]
    (E : Y'.IdealSheafData) (hE : IsStrictNormalCrossingsDivisor (E.comap h)) (x : X') :
    IsRegularLocalRing (Y'.presheaf.stalk (h.base x)) ∧
      ∃ (U : Y'.affineOpens) (hy : h.base x ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y', U.1))
        (J : Finset (Fin n)),
        IsRegularParameterSystem (Y'.presheaf.stalk (h.base x)) n
            (fun i => Y'.presheaf.germ U.1 (h.base x) hy (f i)) ∧
          E.ideal U = Ideal.span {∏ i ∈ J, f i} := by
  obtain ⟨hreg, U', hx, n, g, J, hparams, hideal⟩ := hE x
  have : IsRegularLocalRing (X'.presheaf.stalk x) := hreg
  have hU : IsAffineOpen (h ''ᵁ U'.1) := U'.2.image_of_isOpenImmersion h
  have he : U'.1 ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ U'.1) :=
    le_of_eq (Scheme.Hom.preimage_image_eq h U'.1).symm
  have hy : h.base x ∈ h ''ᵁ U'.1 := ⟨x, hx, rfl⟩
  have : IsIso (h.appLE (h ''ᵁ U'.1) U'.1 he) := isIso_appLE_image h U'.1 he
  have : IsIso (h.stalkMap x) := inferInstance
  let ε : Γ(Y', h ''ᵁ U'.1) ≃+* Γ(X', U'.1) :=
    (asIso (h.appLE (h ''ᵁ U'.1) U'.1 he)).commRingCatIsoToRingEquiv
  let τ : Y'.presheaf.stalk (h.base x) ≃+* X'.presheaf.stalk x :=
    (asIso (h.stalkMap x)).commRingCatIsoToRingEquiv
  have hgerm : ∀ i, τ (Y'.presheaf.germ (h ''ᵁ U'.1) (h.base x) hy (ε.symm (g i)))
      = X'.presheaf.germ U'.1 x hx (g i) := by
    intro i
    have h1 := stalkMap_germ_eq_germ_appLE h (h ''ᵁ U'.1) U'.1 he x hx hy (ε.symm (g i))
    have h2 : (h.appLE (h ''ᵁ U'.1) U'.1 he) (ε.symm (g i)) = g i := ε.apply_symm_apply (g i)
    rw [h2] at h1
    exact h1
  refine ⟨IsRegularLocalRing.of_ringEquiv τ.symm, ⟨h ''ᵁ U'.1, hU⟩, hy, n,
    fun i => ε.symm (g i), J, ?_, ?_⟩
  · refine isRegularParameterSystem_of_ringEquiv τ.symm n
      (fun i => X'.presheaf.germ U'.1 x hx (g i))
      (fun i => Y'.presheaf.germ (h ''ᵁ U'.1) (h.base x) hy (ε.symm (g i))) ?_ hparams
    intro i
    rw [← hgerm i, τ.symm_apply_apply]
  · have hmap := Scheme.IdealSheafData.comap_ideal_eq_map_appLE E h ⟨h ''ᵁ U'.1, hU⟩ U' he
    rw [hideal] at hmap
    have hprod : (ε.symm : Γ(X', U'.1) →+* Γ(Y', h ''ᵁ U'.1)) (∏ i ∈ J, g i)
        = ∏ i ∈ J, ε.symm (g i) := map_prod _ _ _
    rw [ideal_eq_span_of_map_eq_span ((h.appLE (h ''ᵁ U'.1) U'.1 he).hom)
      (ε.symm : Γ(X', U'.1) →+* Γ(Y', h ''ᵁ U'.1)) (fun r => ε.symm_apply_apply r)
      (E.ideal ⟨h ''ᵁ U'.1, hU⟩) (∏ i ∈ J, g i) hmap.symm, hprod]

theorem reducedInverseImage_comp {A B Z : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ Z)
    (W : TopologicalSpace.Closeds Z) :
    reducedInverseImage (g ≫ f) W
      = Scheme.IdealSheafData.vanishingIdeal (closedPreimage g (closedPreimage f W)) := by
  have h : closedPreimage (g ≫ f) W = closedPreimage g (closedPreimage f W) := by
    apply SetLike.ext'
    show (g ≫ f).base ⁻¹' (W : Set Z) = g.base ⁻¹' (f.base ⁻¹' (W : Set Z))
    ext p
    simp
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, h]

theorem comap_reducedInverseImage_of_isOpenImmersion {A B Z : Scheme.{u}} (h : A ⟶ B)
    [IsOpenImmersion h] (f : B ⟶ Z) (W : TopologicalSpace.Closeds Z) :
    (reducedInverseImage f W).comap h = reducedInverseImage (h ≫ f) W := by
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, comap_vanishingIdeal_of_isOpenImmersion,
    reducedInverseImage_comp]

theorem reducedInverseImage_eq_radical {T Y : Scheme.{u}} (f : T ⟶ Y)
    (W : TopologicalSpace.Closeds Y) (J : T.IdealSheafData)
    (hJ : (J.support : Set T) = f.base ⁻¹' (W : Set Y)) :
    reducedInverseImage f W = J.radical := by
  have h : J.support = closedPreimage f W := SetLike.ext' hJ
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, ← h,
    Scheme.IdealSheafData.vanishingIdeal_support]

theorem IsStrictNormalCrossingsDivisor.of_isOpenImmersion_jointly_surjective {X : Scheme.{u}} (D : X.IdealSheafData) {ι : Type v}
    (Y : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ X) (hp : ∀ i, IsOpenImmersion (p i))
    (hsurj : ∀ x : X, ∃ (i : ι) (y : Y i), (p i).base y = x)
    (hD : ∀ i, IsStrictNormalCrossingsDivisor (D.comap (p i))) : IsStrictNormalCrossingsDivisor D := by
  intro x
  obtain ⟨i, y, hy⟩ := hsurj x
  subst hy
  have := hp i
  exact isStrictNormalCrossingsAt_base_of_comap (p i) D (hD i) y

theorem IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod {A B Z : Scheme.{u}} (g : (A ⨿ B) ⟶ Z)
    (W : TopologicalSpace.Closeds Z)
    (hA : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W))
    (hB : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage g W) := by
  intro z
  by_cases hz : z ∈ Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base
  · obtain ⟨a, rfl⟩ := hz
    have h1 : (reducedInverseImage g W).comap (coprod.inl : A ⟶ A ⨿ B)
        = reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W :=
      comap_reducedInverseImage_of_isOpenImmersion _ g W
    refine isStrictNormalCrossingsAt_base_of_comap (coprod.inl : A ⟶ A ⨿ B) (reducedInverseImage g W) ?_ a
    rw [h1]
    exact hA
  · have hz' : z ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := by
      rw [Blowup.range_coprod_inr_eq_compl]
      exact hz
    obtain ⟨b, rfl⟩ := hz'
    have h1 : (reducedInverseImage g W).comap (coprod.inr : B ⟶ A ⨿ B)
        = reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W :=
      comap_reducedInverseImage_of_isOpenImmersion _ g W
    refine isStrictNormalCrossingsAt_base_of_comap (coprod.inr : B ⟶ A ⨿ B) (reducedInverseImage g W) ?_ b
    rw [h1]
    exact hB

end FunctorialResolution.EmbeddedResolution
end
end

