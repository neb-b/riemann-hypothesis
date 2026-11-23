module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0001

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def AffineEmbedsIntoAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p],
    ∃ (n : ℕ) (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))),
      AlgebraicGeometry.IsClosedImmersion e ∧ NonzeroOnComponents e.ker ∧
        e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p

def NilIsStrictNormalCrossingsOnAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u} (Fin n))).IdealSheafData)

def AffineSpaceIsSmooth : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))

def ClosedEmbeddingsRelatedByAutomorphism : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p] (n m : ℕ)
    (e₁ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)))
    [AlgebraicGeometry.IsClosedImmersion e₁]
    (e₂ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)))
    [AlgebraicGeometry.IsClosedImmersion e₂],
    e₁ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p →
    e₂ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin m)) = p →
    ∃ Φ : affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ≅
            affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)),
      Φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) =
          affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) ∧
        AffineSpace.homOfVector p (coordVectorInl n m e₁) ≫ Φ.hom =
          AffineSpace.homOfVector p (coordVectorInr n m e₂)

abbrev AffineResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], SequenceOfBlowups Y

def IsCompatibleWithOpenImmersions (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    [AlgebraicGeometry.IsReduced V] [AlgebraicGeometry.IsAffine V]
    (φ : V ⟶ Y) [AlgebraicGeometry.IsOpenImmersion φ],
    φ ≫ pY = pV → IsPullbackBlowupSequence φ (R k V pV) (R k Y pY)

def IsCompatibleWithEtaleCovers (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y W : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pW : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pW] [AlgebraicGeometry.QuasiCompact pW]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ pY = pW → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) →
    IsStrictPullbackBlowupSeq φ (R k W pW) (R k Y pY)

def IsCompatibleWithFieldBaseChange (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [AlgebraicGeometry.IsReduced (baseChange p K)]
    [AlgebraicGeometry.IsAffine (baseChange p K)],
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K)) (R k Y p)

def IsInducedByAffineRule (R : AffineResolutionRule.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (B : SequenceOfBlowups Y) : Prop :=
  ∀ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ p = q → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) → IsStrictPullbackBlowupSeq φ (R k W q) B

def ExistsGluedBlowupSequence (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithEtaleCovers R →
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y],
    ∃ B : SequenceOfBlowups Y, (∀ i, i < B.length → B.center i ≠ ⊤) ∧ IsInducedByAffineRule R k Y p B

def InducedRuleCompatibleWithFieldExtension (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithOpenImmersions R → IsCompatibleWithFieldBaseChange R →
  ∀ F : ResolutionRule.{u},
    (∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
      IsInducedByAffineRule R k X f (F k X f)) →
    IsCompatibleWithFieldExtension F

end FunctorialResolution.EmbeddedResolution
end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
section
universe u

open CategoryTheory Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem map_eq_ker {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ Y) :
    I.map f = (I.subschemeι ≫ f).ker := rfl

private theorem comap_eq_ker_pullback_fst {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.comap f = (pullback.fst f I.subschemeι).ker := rfl

theorem comap_map_eq_map_comap_of_isPullback {W X X' W' : Scheme.{u}} {f : W ⟶ X} {g : X' ⟶ X}
    {g' : W' ⟶ W} {f' : W' ⟶ X'} (H : IsPullback g' f' f g)
    [QuasiCompact f] [AlgebraicGeometry.Flat g] (I : W.IdealSheafData) :
    (I.map f).comap g = (I.comap g').map f' := by
  have hqc : QuasiCompact (I.subschemeι ≫ f) := inferInstance
  have S : IsPullback (pullback.snd g' I.subschemeι) (pullback.fst g' I.subschemeι ≫ f')
      (I.subschemeι ≫ f) g := (IsPullback.of_hasPullback g' I.subschemeι).flip.paste_vert H
  have hqc' : QuasiCompact (pullback.fst g' I.subschemeι ≫ f') := quasiCompact_of_isPullback S
  have h1 := ker_eq_comap_ker_of_isPullback_of_flat S
  rw [map_eq_ker, ← h1, Scheme.Hom.ker_comp, comap_eq_ker_pullback_fst]

theorem comap_map_eq_self_of_isPullback {W X Q : Scheme.{u}} (γ : W ⟶ X)
    [QuasiCompact γ] [AlgebraicGeometry.Flat γ] {p q : Q ⟶ W} (H : IsPullback p q γ γ)
    (I : W.IdealSheafData) (hI : I.comap p = I.comap q) :
    (I.map γ).comap γ = I := by
  have key := comap_map_eq_map_comap_of_isPullback H I
  rw [hI] at key
  rw [key]
  obtain ⟨s, hsq⟩ : ∃ s : W ⟶ Q, s ≫ q = 𝟙 W :=
    ⟨H.lift (𝟙 W) (𝟙 W) rfl, H.lift_snd _ _ _⟩
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap I q)
  have h1 := Scheme.IdealSheafData.comap_map_le (I.comap q) q
  have h2 : (((I.comap q).map q).comap q).comap s ≤ ((I.comap q).comap s) :=
    Scheme.IdealSheafData.comap_mono s h1
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hsq,
    Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at h2

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothAffineLiftRelativeDimension
section
universe u

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace SmoothChartRelativeDimension

private def tensorProductLiftRingHom {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) : (R ⊗[S] C) →+* T :=
  letI : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  letI : Algebra R T := a.toAlgebra
  haveI : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom S R T)
      ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T)).toRingHom

private theorem tensorProductLiftRingHom_tmul {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) (x : R) (y : C) :
    tensorProductLiftRingHom a b hab (x ⊗ₜ[S] y) = a x * b y := by
  let _ : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  let _ : Algebra R T := a.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.TensorProduct.productMap_apply_tmul (IsScalarTower.toAlgHom S R T)
    ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T) x y

theorem exists_affineOpen_isStandardSmoothOfRelativeDimension {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : AlgebraicGeometry.IsAffineOpen V),
      RingHom.IsStandardSmoothOfRelativeDimension r
        (CommRingCat.Hom.hom ((V.ι ≫ h).appTop)) := by
  obtain ⟨U, hU, V, hV, hyV, e, hss⟩ := ‹AlgebraicGeometry.SmoothOfRelativeDimension r h›.1 y
  have hmemU : h.base y ∈ U := e hyV
  obtain ⟨f₀, hf₀le, hf₀mem⟩ :=
    (isAffineOpen_top X).exists_basicOpen_le (⟨h.base y, hmemU⟩ : ↥U) (by trivial)
  set g : Γ(X, U) :=
    (ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) f₀ with hgdef
  set s : Γ(Y, V) := (ConcreteCategory.hom (h.appLE U V e)) g with hsdef
  have hsg : s = (CommRingCat.Hom.hom (h.appLE U V e)) g := rfl
  have hbg : X.basicOpen g = U ⊓ X.basicOpen f₀ :=
    Scheme.basicOpen_res X f₀ (homOfLE (le_top : U ≤ ⊤)).op
  have hbgf : X.basicOpen g = X.basicOpen f₀ := hbg.trans (inf_eq_right.mpr hf₀le)
  have hbs : Y.basicOpen s = V ⊓ h ⁻¹ᵁ X.basicOpen g :=
    Scheme.basicOpen_appLE h V U e g
  have hyW : y ∈ Y.basicOpen s := by
    rw [hbs]
    refine ⟨hyV, ?_⟩
    show h.base y ∈ X.basicOpen g
    rw [hbgf]
    exact hf₀mem
  have hWaff : IsAffineOpen (Y.basicOpen s) := hV.basicOpen s
  have hle₂ : Y.basicOpen s ≤ h ⁻¹ᵁ X.basicOpen g := by
    rw [hbs]; exact inf_le_right
  have hle₃ : Y.basicOpen s ≤ h ⁻¹ᵁ (⊤ : X.Opens) := by
    intro z hz; trivial
  have hbgU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hWV : Y.basicOpen s ≤ V := Y.basicOpen_le s
  have hmm : Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
      = Submonoid.powers s := by
    ext x
    constructor
    · rintro ⟨y', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_pow, hsg]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨g ^ n, ⟨n, rfl⟩, by rw [map_pow, hsg]⟩
  have hlocX : IsLocalization (Submonoid.powers g) (Γ(X, X.basicOpen g) : Type u) :=
    hU.isLocalization_basicOpen g
  have hlocY : IsLocalization
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g))
      (Γ(Y, Y.basicOpen s) : Type u) := by
    rw [hmm]
    exact hV.isLocalization_basicOpen s
  have hloc := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves r
    (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
    (Γ(X, X.basicOpen g) : Type u) (Γ(Y, Y.basicOpen s) : Type u) hss
  have hle_sub : Submonoid.powers g ≤ Submonoid.comap (CommRingCat.Hom.hom (h.appLE U V e))
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)) :=
    fun x hx => ⟨x, hx, rfl⟩
  have hloc2 : RingHom.IsStandardSmoothOfRelativeDimension r
      (IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub) := hloc
  have arrow : h.appLE U V e ≫ Y.presheaf.map (homOfLE hWV).op
      = X.presheaf.map (homOfLE hbgU).op ≫ h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have key : IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub
      = CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
    rw [IsLocalization.map_comp]
    exact congrArg CommRingCat.Hom.hom arrow
  have hP : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)) := by
    rw [← key]
    exact hloc2
  let _ : Algebra (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u) :=
    (CommRingCat.Hom.hom
      (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op)).toAlgebra
  have : IsLocalization.Away f₀ (Γ(X, X.basicOpen g) : Type u) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen f₀
      (homOfLE (le_top : X.basicOpen g ≤ ⊤)) hbgf
  have hsrc :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway r).1
  have hcomp0 : RingHom.IsStandardSmoothOfRelativeDimension r
      ((CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)).comp
        (algebraMap (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u))) :=
    hsrc _ f₀ _ hP
  have hmap : X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op ≫
      h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ = h.appLE ⊤ (Y.basicOpen s) hle₃ :=
    Scheme.Hom.map_appLE h hle₂ (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op
  have hcomp : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE ⊤ (Y.basicOpen s) hle₃)) := by
    rw [← hmap, CommRingCat.hom_comp]
    exact hcomp0
  have hA : ((Y.basicOpen s).ι ''ᵁ ⊤) ≤ (⊤ : Y.Opens) := le_top
  have hBeq : ((Y.basicOpen s).ι ''ᵁ ⊤) = Y.basicOpen s := by simp
  have hB : Y.basicOpen s ≤ ((Y.basicOpen s).ι ''ᵁ ⊤) := le_of_eq hBeq.symm
  have hclean : h.appTop ≫ (Y.presheaf.map (homOfLE hA).op ≫ Y.presheaf.map (homOfLE hB).op)
      = h.appLE (⊤ : X.Opens) (Y.basicOpen s) hle₃ := by
    rw [← Functor.map_comp]
    rfl
  have hiso : ((Y.basicOpen s).ι ≫ h).appTop ≫ (Y.basicOpen s).topIso.hom
      = h.appLE ⊤ (Y.basicOpen s) hle₃ := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
    exact hclean
  have hgoal : ((Y.basicOpen s).ι ≫ h).appTop
      = h.appLE ⊤ (Y.basicOpen s) hle₃ ≫ (Y.basicOpen s).topIso.inv :=
    (Iso.eq_comp_inv _).mpr hiso
  refine ⟨Y.basicOpen s, hyW, hWaff, ?_⟩
  rw [hgoal]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := r)).1 _
    (Y.basicOpen s).topIso.symm.commRingCatIsoToRingEquiv hcomp

theorem exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension {S R B : CommRingCat.{u}}
    (ι : S ⟶ R) (hι : Function.Surjective ⇑(CommRingCat.Hom.hom ι)) (φ : R ⟶ B) (r : ℕ)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom φ)) :
    ∃ (B' : CommRingCat.{u}) (σ : S ⟶ B') (ψ : B' ⟶ B),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        Function.Surjective ⇑(CommRingCat.Hom.hom ψ) ∧
        CategoryTheory.IsPushout ι σ φ ψ := by
  let _ : Algebra (S : Type u) (R : Type u) := (CommRingCat.Hom.hom ι).toAlgebra
  let _ : Algebra (R : Type u) (B : Type u) := (CommRingCat.Hom.hom φ).toAlgebra
  let _ : Algebra (S : Type u) (B : Type u) :=
    ((CommRingCat.Hom.hom φ).comp (CommRingCat.Hom.hom ι)).toAlgebra
  have : IsScalarTower (S : Type u) (R : Type u) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension r (R : Type u) (B : Type u) := hφ
  obtain ⟨C, hCring, hCalg, f, hss, hfs, e, he⟩ :=
    FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension (S : Type u) (R : Type u)
      (B : Type u) r hι
  have : Algebra.IsStandardSmoothOfRelativeDimension r (S : Type u) C := hss
  have hcond : ι ≫ φ = CommRingCat.ofHom (algebraMap (S : Type u) C) ≫
      CommRingCat.ofHom f.toRingHom := by
    refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
    exact (f.commutes s).symm
  have hcc : ∀ (c : CategoryTheory.Limits.PushoutCocone ι
        (CommRingCat.ofHom (algebraMap (S : Type u) C))) (s : (S : Type u)),
      (CommRingCat.Hom.hom c.inl) (algebraMap (S : Type u) (R : Type u) s)
        = (CommRingCat.Hom.hom c.inr) (algebraMap (S : Type u) C s) := fun c s =>
    congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) c.condition
  have facR : ∀ c : CategoryTheory.Limits.PushoutCocone ι
      (CommRingCat.ofHom (algebraMap (S : Type u) C)),
      CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom) = c.inr := by
    intro c
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    show tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)
        (e.symm (f z)) = (CommRingCat.Hom.hom c.inr) z
    rw [show e.symm (f z) = (1 : (R : Type u)) ⊗ₜ[(S : Type u)] z from
      e.symm_apply_eq.mpr (he z).symm, tensorProductLiftRingHom_tmul, map_one, one_mul]
  refine ⟨CommRingCat.of C, CommRingCat.ofHom (algebraMap (S : Type u) C),
    CommRingCat.ofHom f.toRingHom, ?_, ?_, ?_⟩
  · exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap r).mpr hss
  · exact hfs
  · refine CategoryTheory.IsPushout.of_isColimit' ⟨hcond⟩
      (CategoryTheory.Limits.PushoutCocone.IsColimit.mk hcond
        (fun c => CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) ?_ facR ?_)
    · intro c
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      obtain ⟨s, rfl⟩ := hι x
      have key : ι ≫ (φ ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) = ι ≫ c.inl := by
        rw [← Category.assoc, hcond, Category.assoc, facR c, ← c.condition]
      exact congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) key
    · intro c m h₁ h₂
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      obtain ⟨z, rfl⟩ := hfs b
      exact congrArg (fun t : CommRingCat.of C ⟶ c.pt => (CommRingCat.Hom.hom t) z)
        (h₂.trans (facR c).symm)

end SmoothChartRelativeDimension

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem generalizingMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    GeneralizingMap (fun x : ↥X => f x) :=
  AlgebraicGeometry.Flat.generalizingMap f

theorem closure_image_mem_irreducibleComponents_of_generalizingMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y := by
  have hcont : Continuous (fun x : ↥X => f x) := f.continuous
  have hCirr : IsIrreducible C := hC.1
  have hCmax : ∀ ⦃b : Set ↥X⦄, IsIrreducible b → C ≤ b → b ≤ C := hC.2
  have hCcl : closure C = C :=
    subset_antisymm (hCmax hCirr.closure subset_closure) subset_closure
  have hCclosed : IsClosed C := by rw [← hCcl]; exact isClosed_closure
  obtain ⟨η, hη⟩ := QuasiSober.sober hCirr hCclosed
  have hη' : closure ({η} : Set ↥X) = C := hη
  have hηC : η ∈ C := by rw [← hη']; exact subset_closure rfl
  have key : closure ((fun x : ↥X => f x) '' C) = closure ({f η} : Set ↥Y) := by
    have h1 : (fun x : ↥X => f x) '' C ⊆ closure ({f η} : Set ↥Y) := by
      rw [← hη']
      intro w hw
      have hw2 := image_closure_subset_closure_image hcont hw
      rwa [Set.image_singleton] at hw2
    have h2 : ({f η} : Set ↥Y) ⊆ (fun x : ↥X => f x) '' C :=
      Set.singleton_subset_iff.mpr (Set.mem_image_of_mem _ hηC)
    exact subset_antisymm (closure_minimal h1 isClosed_closure) (closure_mono h2)
  have hmax : ∀ y : ↥Y, y ⤳ f η → y = f η := by
    intro y hy
    obtain ⟨x', hx'η, hfx'⟩ := hf hy
    have h1 : η ∈ closure ({x'} : Set ↥X) := specializes_iff_mem_closure.mp hx'η
    have h2 : C ⊆ closure ({x'} : Set ↥X) := by
      rw [← hη']
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure
    have h3 : closure ({x'} : Set ↥X) ⊆ C := hCmax isIrreducible_singleton.closure h2
    have hx'C : x' ∈ C := h3 (subset_closure rfl)
    have hηx' : η ⤳ x' := specializes_iff_mem_closure.mpr (by rw [hη']; exact hx'C)
    have hA : nhds x' ≤ nhds η := hx'η
    have hB : nhds η ≤ nhds x' := hηx'
    have hins : Inseparable x' η := le_antisymm hA hB
    have hxx : x' = η := hins.eq
    rw [← hfx', hxx]
  rw [key]
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro Z hZ hsub
  have hZ' : IsIrreducible Z := hZ
  have hsub' : closure ({f η} : Set ↥Y) ⊆ Z := hsub
  obtain ⟨z, hz⟩ := QuasiSober.sober hZ'.closure isClosed_closure
  have hz' : closure ({z} : Set ↥Y) = closure Z := hz
  have h1 : f η ∈ closure ({z} : Set ↥Y) := by
    rw [hz']
    exact subset_closure (hsub' (subset_closure rfl))
  have h2 : z = f η := hmax z (specializes_iff_mem_closure.mpr h1)
  show Z ⊆ closure ({f η} : Set ↥Y)
  intro w hw
  rw [← h2, hz']
  exact subset_closure hw

theorem support_comap {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set ↥X) = (fun x : ↥X => f x) ⁻¹' (I.support : Set ↥Y) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap I f]
  rfl

namespace NonzeroOnComponents

theorem comap_of_generalizingMap {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y)
    (hf : GeneralizingMap (fun x : ↥X => f x)) :
    NonzeroOnComponents (I.comap f) := by
  intro T hT hsub
  have hsub' : closure ((fun x : ↥X => f x) '' T) ⊆ (I.support : Set ↥Y) := by
    refine closure_minimal ?_ I.support.2
    rintro _ ⟨x, hxT, rfl⟩
    have hx : x ∈ ((I.comap f).support : Set ↥X) := hsub hxT
    rw [support_comap f I] at hx
    exact hx
  exact hI _ (closure_image_mem_irreducibleComponents_of_generalizingMap f hf hT) hsub'

theorem comap_of_flat {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f (generalizingMap_of_flat f)

theorem comap_of_isOpenImmersion {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f f.isOpenEmbedding.generalizingMap

end NonzeroOnComponents

theorem closure_image_mem_irreducibleComponents_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y :=
  closure_image_mem_irreducibleComponents_of_generalizingMap f (generalizingMap_of_flat f) hC

end FunctorialResolution.EmbeddedResolution
end
end

