module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionSmooth
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem chartToLastObj_comp_lastStructMap_assoc (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    d.chartToLastObj j ≫ (s.lastStructMap ≫ f) = (d.seq j).lastStructMap ≫ (d.cover.f j ≫ f) := by
  rw [← Category.assoc, d.chartToLastObj_comp_lastStructMap j, Category.assoc]

private theorem ringHom_smooth_appTop_of_smooth {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (hg : AlgebraicGeometry.Smooth g) (i : 𝒲.I₀) :
    RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom) :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mp hg i

private theorem smooth_of_ringHom_smooth_appTop {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (h : ∀ i : 𝒲.I₀, RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom)) :
    AlgebraicGeometry.Smooth g :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mpr h

private theorem smooth_chartToLastObj_comp (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    AlgebraicGeometry.Smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f)) := by
  rw [d.chartToLastObj_comp_lastStructMap_assoc j]
  exact (d.isResolution j).1

private theorem smooth_appTop_affineCover_chartToLastObj (d : LocalResolutionData k f s) (j : d.cover.I₀)
    (a : ((d.seq j).lastObj.affineCover).I₀) :
    RingHom.Smooth (((((d.seq j).lastObj.affineCover).f a ≫ d.chartToLastObj j)
      ≫ (s.lastStructMap ≫ f)).appTop.hom) := by
  have h := ringHom_smooth_appTop_of_smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f))
    ((d.seq j).lastObj.affineCover) (smooth_chartToLastObj_comp d j) a
  rw [Category.assoc]
  exact h

theorem smooth_lastStructMap_comp (d : LocalResolutionData k f s) :
    AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) := by
  have haffine : ∀ i : (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).I₀,
      AlgebraicGeometry.IsAffine
        ((d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).X i) := by
    rintro ⟨j, a⟩
    exact inferInstanceAs (AlgebraicGeometry.IsAffine (((d.lastObjCover.X j).affineCover).X a))
  refine smooth_of_ringHom_smooth_appTop (s.lastStructMap ≫ f)
    (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover) ?_
  rintro ⟨j, a⟩
  exact smooth_appTop_affineCover_chartToLastObj d j a

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionStrictNormalCrossings
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem support_vanishingIdeal_eq {Y : Scheme.{u}} (Z : Closeds ↥Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

private theorem comap_vanishingIdeal_of_isOpenImmersion {Y T : Scheme.{u}} (g : T ⟶ Y)
    [IsOpenImmersion g] (Z : Closeds ↥Y) (W : Closeds ↥T)
    (hW : (W : Set ↥T) = g.base ⁻¹' (Z : Set ↥Y)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap g
      = Scheme.IdealSheafData.vanishingIdeal W := by
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap g := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).support = W := by
    rw [Scheme.IdealSheafData.support_comap, support_vanishingIdeal_eq]
    exact TopologicalSpace.Closeds.ext hW.symm
  rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

private theorem isRegularParameterSystem_map_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R)
    (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n (fun i => e (x i)) := by
  unfold IsRegularParameterSystem at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · have hmax : Ideal.comap (e : R →+* S) (IsLocalRing.maximalIdeal S)
        = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective (e : R →+* S) e.surjective)
    have hm : Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R)
        = IsLocalRing.maximalIdeal S := by
      rw [← hmax]
      exact Ideal.map_comap_of_surjective (e : R →+* S) e.surjective _
    have himg : Ideal.span (Set.range fun i => e (x i))
        = Ideal.map (e : R →+* S) (Ideal.span (Set.range x)) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [himg, h1, hm]
  · rw [h2]
    exact ringKrullDim_eq_of_ringEquiv e

private theorem isRegularParameterSystem_of_ringEquiv_apply_eq {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R) (y : Fin n → S)
    (hxy : ∀ i, e (x i) = y i) (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n y := by
  have hy : y = fun i => e (x i) := (funext fun i => hxy i).symm
  subst hy
  exact isRegularParameterSystem_map_ringEquiv e n x h

private theorem surjective_iso_inv {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Surjective (CommRingCat.Hom.hom e.inv) := by
  intro a
  refine ⟨(CommRingCat.Hom.hom e.hom) a, ?_⟩
  simp

private theorem map_eqToHom_germ {T : Scheme.{u}} {U V : T.Opens}
    (h : Opposite.op U = Opposite.op V) (z : ↥T) (hz : z ∈ U) (hz' : z ∈ V) :
    T.presheaf.map (eqToHom h) ≫ T.presheaf.germ V z hz' = T.presheaf.germ U z hz := by
  have h' : U = V := congrArg Opposite.unop h
  subst h'
  simp

private theorem appIso_inv_germ_stalkMap {Y T : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g]
    (U : T.Opens) (z : ↥T) (hz : z ∈ U) (hgz : g.base z ∈ (g ''ᵁ U : Y.Opens)) :
    (Scheme.Hom.appIso g U).inv ≫ Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫
        Scheme.Hom.stalkMap g z = T.presheaf.germ U z hz := by
  have h1 : Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫ Scheme.Hom.stalkMap g z
      = Scheme.Hom.app g (g ''ᵁ U) ≫ T.presheaf.germ (g ⁻¹ᵁ (g ''ᵁ U)) z hgz :=
    Scheme.Hom.germ_stalkMap g (g ''ᵁ U) z hgz
  rw [h1, ← Category.assoc]
  simp
  exact map_eqToHom_germ _ z hz hgz

private theorem appIso_inv_germ_stalkMap_apply {Y T : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g]
    (U : T.Opens) (z : ↥T) (hz : z ∈ U) (hgz : g.base z ∈ (g ''ᵁ U : Y.Opens))
    (a : Γ(T, U)) :
    (ConcreteCategory.hom (Scheme.Hom.stalkMap g z))
        ((ConcreteCategory.hom (Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz))
          ((ConcreteCategory.hom (Scheme.Hom.appIso g U).inv) a))
      = (ConcreteCategory.hom (T.presheaf.germ U z hz)) a := by
  have h := congrArg (fun m : Γ(T, U) ⟶ T.presheaf.stalk z => (ConcreteCategory.hom m) a)
    (appIso_inv_germ_stalkMap g U z hz hgz)
  simpa only [CommRingCat.comp_apply] using h

theorem chartToLastObj_preimage_smoothLocusComplement (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.chartToLastObj i).base ⁻¹'
        (s.lastStructMap.base ⁻¹' ((smoothLocusComplement f : Closeds ↥X) : Set ↥X))
      = (d.seq i).lastStructMap.base ⁻¹'
        ((smoothLocusComplement (d.cover.f i ≫ f) : Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have hcomp := d.chartToLastObj_comp_lastStructMap i
  have hsl := d.preimage_smoothLocusComplement_cover_map i
  ext x
  simp only [Set.mem_preimage]
  have hx : s.lastStructMap.base ((d.chartToLastObj i).base x)
      = (d.cover.f i).base ((d.seq i).lastStructMap.base x) := by
    have h := congrArg (fun g : (d.seq i).lastObj ⟶ X => g.base x) hcomp
    simpa using h
  rw [hx, ← Set.mem_preimage, hsl]

theorem comap_reducedInverseImage_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (reducedInverseImage s.lastStructMap (smoothLocusComplement f)).comap (d.chartToLastObj i)
      = reducedInverseImage (d.seq i).lastStructMap (smoothLocusComplement (d.cover.f i ≫ f)) := by
  have h1 := d.chartToLastObj_preimage_smoothLocusComplement i
  unfold reducedInverseImage
  exact comap_vanishingIdeal_of_isOpenImmersion (d.chartToLastObj i) _ _ h1.symm

private theorem isStrictNormalCrossingsDivisor_of_openCover {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (H : ∀ y : ↥Y, ∃ (T : Scheme.{u}) (g : T ⟶ Y) (_ : IsOpenImmersion g) (z : ↥T),
      g.base z = y ∧ IsStrictNormalCrossingsDivisor (I.comap g)) : IsStrictNormalCrossingsDivisor I := by
  intro y
  obtain ⟨T, g, hg, z, hzy, hSNC⟩ := H y
  subst hzy
  have := hg
  obtain ⟨hreg, U, hzU, n, F, J, hpar, hid⟩ := hSNC z
  have : IsRegularLocalRing ↑(T.presheaf.stalk z) := hreg
  obtain ⟨E, hE⟩ : ∃ E : (↑(Y.presheaf.stalk (g.base z)) : Type u) ≃+* ↑(T.presheaf.stalk z),
      ∀ x, E x = (ConcreteCategory.hom (Scheme.Hom.stalkMap g z)) x :=
    ⟨(asIso (Scheme.Hom.stalkMap g z)).commRingCatIsoToRingEquiv, fun _ => rfl⟩
  have hgz : g.base z ∈ (g ''ᵁ (U : T.Opens) : Y.Opens) := ⟨z, hzU, rfl⟩
  have hVaff : IsAffineOpen (g ''ᵁ (U : T.Opens)) :=
    (U.2 : IsAffineOpen (U : T.Opens)).image_of_isOpenImmersion g
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) :=
    surjective_iso_inv (Scheme.Hom.appIso g (U : T.Opens))
  refine ⟨IsRegularLocalRing.of_ringEquiv E.symm,
    ⟨g ''ᵁ (U : T.Opens), hVaff⟩, hgz, n,
    fun i => (ConcreteCategory.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i), J, ?_, ?_⟩
  · refine isRegularParameterSystem_of_ringEquiv_apply_eq E.symm n _ _ ?_ hpar
    intro i
    have hgerm := appIso_inv_germ_stalkMap_apply g (U : T.Opens) z hzU hgz (F i)
    rw [← hE] at hgerm
    rw [← hgerm, E.symm_apply_apply]
  · have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I g U
    rw [hid] at h1
    have h2 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.span {∏ i ∈ J, F i})
        = Ideal.span {∏ i ∈ J,
            (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i)} := by
      rw [Ideal.map_span, Set.image_singleton, map_prod]
    have h3 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.comap (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
          (I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩))
        = I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩ :=
      Ideal.map_comap_of_surjective _ hsurj _
    exact (h3.symm.trans
      (congrArg (Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv))
        h1.symm)).trans h2

theorem isStrictNormalCrossingsDivisor_reducedInverseImage (d : LocalResolutionData k f s) [LocallyOfFinitePresentation f] :
    IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f)) := by
  refine isStrictNormalCrossingsDivisor_of_openCover _ ?_
  intro y
  obtain ⟨i, z, hz⟩ := d.exists_chartToLastObj_eq y
  refine ⟨(d.seq i).lastObj, d.chartToLastObj i, inferInstance, z, hz, ?_⟩
  rw [d.comap_reducedInverseImage_chartToLastObj i]
  exact (d.isResolution i).2.2.2.2.2

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusIsomorphism
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem isPullback_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsPullback (d.chartToLastObj i) ((d.seq i).lastStructMap) s.lastStructMap (d.cover.f i) := by
  have hsq : CommSq ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    ⟨(d.chartToLastObj_comp_lastStructMap i).symm⟩
  have h : IsPullback ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    IsPullback.of_iso_pullback hsq (d.lastObjIsoPullback i) (d.lastObjIsoPullback_hom_fst i)
      (d.chartToLastObj_eq i).symm
  exact h.flip

private theorem isIso_pullback_snd_restrict_smoothLocus (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsIso (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
  have hp := isPullback_morphismRestrict s.lastStructMap f.smoothLocus
  have hc := isPullback_morphismRestrict (d.cover.f i) f.smoothLocus
  have ht := isPullback_morphismRestrict ((d.seq i).lastStructMap) (d.cover.f i ⁻¹ᵁ f.smoothLocus)
  have hbig := ht.paste_vert (d.isPullback_chartToLastObj i).flip
  have hw : (((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) ≫
        (d.cover.f i ∣_ f.smoothLocus)) ≫ f.smoothLocus.ι
      = ((((d.seq i).lastStructMap ⁻¹ᵁ (d.cover.f i ⁻¹ᵁ f.smoothLocus)).ι) ≫ d.chartToLastObj i)
        ≫ s.lastStructMap := by
    rw [Category.assoc, hc.w]
    exact hbig.w
  have hsq : IsPullback ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus))
      (hp.lift _ _ hw) (d.cover.f i ∣_ f.smoothLocus) (s.lastStructMap ∣_ f.smoothLocus) := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [hp.lift_snd, hc.w]
      exact hbig
    · rw [hp.lift_fst]
  have hiso : IsIso ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact (d.isResolution i).2.2.1
  have hcomp : IsIso (hsq.flip.isoPullback.hom ≫
      pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
    rw [hsq.flip.isoPullback_hom_snd]
    exact hiso
  exact IsIso.of_isIso_comp_left hsq.flip.isoPullback.hom
    (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus))

private theorem exists_restrict_smoothLocus_apply_eq (d : LocalResolutionData k f s) :
    ∀ x : ↥(f.smoothLocus.toScheme), ∃ (i : d.cover.I₀)
      (y : ↥((d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)),
        (d.cover.f i ∣_ f.smoothLocus) y = x := by
  intro x
  have hsup : (⨆ i, (d.cover.f i).opensRange) = ⊤ := d.cover.iSup_opensRange
  have hx : (x.1 : ↥X) ∈ (⨆ i, (d.cover.f i).opensRange : X.Opens) := by
    rw [hsup]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hi' : (x.1 : ↥X) ∈ Set.range (d.cover.f i).base := hi
  obtain ⟨y₀, hy₀⟩ := hi'
  have hmem : y₀ ∈ (d.cover.f i ⁻¹ᵁ f.smoothLocus) := by
    show (d.cover.f i).base y₀ ∈ f.smoothLocus
    rw [hy₀]
    exact x.2
  refine ⟨i, ⟨y₀, hmem⟩, ?_⟩
  have h2 := congrFun (morphismRestrict_base (d.cover.f i) f.smoothLocus) ⟨y₀, hmem⟩
  refine h2.trans (Subtype.ext ?_)
  exact hy₀

private def smoothLocusOpenCover (d : LocalResolutionData k f s) :
    Scheme.OpenCover.{u, u} (f.smoothLocus.toScheme) :=
  Scheme.Cover.mkOfCovers d.cover.I₀
    (fun i => (d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)
    (fun i => d.cover.f i ∣_ f.smoothLocus)
    (exists_restrict_smoothLocus_apply_eq d)
    (fun i => show IsOpenImmersion (d.cover.f i ∣_ f.smoothLocus) from inferInstance)

theorem isIso_lastStructMap_restrict_smoothLocus (d : LocalResolutionData k f s) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  have hh : ∀ i : d.cover.I₀, MorphismProperty.isomorphisms Scheme.{u}
      (Scheme.Cover.pullbackHom (smoothLocusOpenCover d) (s.lastStructMap ∣_ f.smoothLocus) i) := by
    intro i
    exact isIso_pullback_snd_restrict_smoothLocus d i
  have key : MorphismProperty.isomorphisms Scheme.{u} (s.lastStructMap ∣_ f.smoothLocus) :=
    IsZariskiLocalAtTarget.of_openCover (smoothLocusOpenCover d) hh
  exact key

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

