module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing

namespace GlobalTheory

namespace FibreFlat

section Algebra

variable {T : Type*} (K : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
  [Algebra T K] [IsFractionRing T K]

theorem includeRight_bijective {C : Type*} [CommRing C] [Algebra T C] {π : T} (hπ : Irreducible π)
    (hu : IsUnit (algebraMap T C π)) :
    Function.Bijective (Algebra.TensorProduct.includeRight : C →ₐ[T] K ⊗[T] C) := by
  have h : Algebra.algebraMapSubmonoid C (nonZeroDivisors T) ≤ IsUnit.submonoid C := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero ht) hπ
    change IsUnit _
    rw [map_mul, map_pow]
    exact (u.isUnit.map _).mul (hu.pow n)
  have h2 : Function.Bijective (algebraMap C (C ⊗[T] K)) :=
    (IsLocalization.atUnits C (S := C ⊗[T] K) _ h).bijective
  exact (Algebra.TensorProduct.comm T C K).bijective.comp h2

theorem ringHom_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra T A] [Algebra T B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat T B] (φ : A →ₐ[T] B)
    (hK : (Algebra.TensorProduct.map (AlgHom.id T K) φ : K ⊗[T] A →+* K ⊗[T] B).Flat)
    (hκ : (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
      ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat) : (φ : A →+* B).Flat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have key : ∀ (P : Ideal B) [P.IsPrime],
      (((IsScalarTower.toAlgHom T B (Localization.AtPrime P)).comp φ : A →ₐ[T] _) :
        A →+* Localization.AtPrime P).Flat := by
    intro P _
    let l := IsScalarTower.toAlgHom T B (Localization.AtPrime P)
    have hl : (l : B →+* Localization.AtPrime P).Flat :=
      RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ P.primeCompl)
    have hbc : ∀ (L : Type _) [CommRing L] [Algebra T L],
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat →
        (Algebra.TensorProduct.map (AlgHom.id T L) (l.comp φ) :
          L ⊗[T] A →+* L ⊗[T] Localization.AtPrime P).Flat := by
      intro L _ _ h
      rw [Algebra.TensorProduct.map_id_comp]
      exact h.comp (RingHom.Flat.lTensor (S := T) L hl)
    by_cases hu : IsUnit (algebraMap T (Localization.AtPrime P) π)
    · have := IsLocalization.flat K (nonZeroDivisors T)
      refine ringHom_flat_of_square
        (α := (Algebra.TensorProduct.includeRight : A →ₐ[T] K ⊗[T] A))
        (β := (Algebra.TensorProduct.includeRight : _ →ₐ[T] K ⊗[T] Localization.AtPrime P))
        (φ' := (Algebra.TensorProduct.map (AlgHom.id T K) (l.comp φ) :
          K ⊗[T] A →+* K ⊗[T] Localization.AtPrime P)) (by ext a; simp [l]) ?_
        (.of_bijective (includeRight_bijective K hπ hu)) ?_
      · have h1 : (algebraMap A (A ⊗[T] K)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
        exact h1.comp (g := (Algebra.TensorProduct.comm T A K : A ⊗[T] K →+* K ⊗[T] A))
          (.of_bijective (Algebra.TensorProduct.comm T A K).bijective)
      · rw [Algebra.TensorProduct.map_id_comp]
        exact hK.comp (RingHom.Flat.lTensor (S := T) K hl)
    · have : IsLocalHom (algebraMap T (Localization.AtPrime P)) := by
        refine ((local_hom_TFAE (algebraMap T (Localization.AtPrime P))).out 1 3).mpr ?_
        rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
          Ideal.span_singleton_le_iff_mem]
        exact hu
      exact flat_of_flat_residueField_baseChange_dvr _ (hbc _ hκ)
  letI := (φ : A →+* B).toAlgebra
  change Module.Flat A B
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun P _ => ?_
  exact RingHom.flat_algebraMap_iff.mp (key P)

end Algebra

def FlatOver {X Y S S' : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S' ⟶ S) : Prop :=
  ∀ ⦃W Z : Scheme.{0}⦄ (a : W ⟶ X) (b : W ⟶ Z) (j : Z ⟶ Y) (h : Z ⟶ S'),
    IsPullback a b f j → j ≫ g = h ≫ s → Flat b

variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}

theorem FlatOver.target (H : FlatOver f g s) {X' Y' : Scheme.{0}} {a' : X' ⟶ X} {f' : X' ⟶ Y'}
    {u : Y' ⟶ Y} (sq : IsPullback a' f' f u) : FlatOver f' (u ≫ g) s :=
  fun _ _ a b j h sq' e => H (a ≫ a') b (j ≫ u) h (sq'.paste_horiz sq) (by simpa using e)

theorem FlatOver.source (H : FlatOver f g s) {X' : Scheme.{0}} (i : X' ⟶ X) [Flat i] :
    FlatOver (i ≫ f) g s := by
  intro W Z a b j h sq e
  have h1 := H _ _ j h (IsPullback.of_hasPullback f j) e
  let c : W ⟶ pullback f j := pullback.lift (a ≫ i) b (by simpa using sq.w)
  have hc : c ≫ pullback.snd f j = b := pullback.lift_snd _ _ _
  have sq2 : IsPullback a c i (pullback.fst f j) :=
    IsPullback.of_bot (by rw [hc]; exact sq) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback f j)
  have h2 : Flat c := MorphismProperty.of_isPullback sq2 ‹Flat i›
  rw [← hc]
  infer_instance

theorem flatOver_of_pullback {X Y : Over S} (φ : X ⟶ Y) (s : S' ⟶ S)
    (H : Flat ((Over.pullback s).map φ).left) : FlatOver φ.left Y.hom s := by
  intro W Z a b j h sq e
  have sq0 : IsPullback (pullback.fst X.hom s) ((Over.pullback s).map φ).left φ.left
      (pullback.fst Y.hom s) := by
    have e1 : ((Over.pullback s).map φ).left ≫ pullback.fst Y.hom s =
        pullback.fst X.hom s ≫ φ.left := pullback.lift_fst _ _ _
    have e2 : ((Over.pullback s).map φ).left ≫ pullback.snd Y.hom s =
        pullback.snd X.hom s := pullback.lift_snd _ _ _
    refine IsPullback.of_bot ?_ e1.symm (IsPullback.of_hasPullback Y.hom s)
    rw [e2, Over.w]
    exact IsPullback.of_hasPullback X.hom s
  let j' : Z ⟶ pullback Y.hom s := pullback.lift j h e
  have hj : j' ≫ pullback.fst Y.hom s = j := pullback.lift_fst _ _ _
  let a' := sq0.lift a (b ≫ j') (by rw [Category.assoc, hj]; exact sq.w)
  have sq1 : IsPullback a' b ((Over.pullback s).map φ).left j' :=
    IsPullback.of_right (by rw [hj, sq0.lift_fst]; exact sq) (sq0.lift_snd _ _ _) sq0
  exact MorphismProperty.of_isPullback sq1 H

theorem FlatOver.tensor {T L A B : Type} [CommRing T] [CommRing L] [CommRing A] [CommRing B]
    [Algebra T L] [Algebra T A] [Algebra T B] (φ : A →ₐ[T] B)
    (H : FlatOver (spMap (φ : A →+* B)) (spMap (algebraMap T A)) (spMap (algebraMap T L))) :
    (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat := by
  have hA := CommRingCat.isPushout_tensorProduct T L A
  have hB := CommRingCat.isPushout_tensorProduct T L B
  have sq : IsPushout (CommRingCat.ofHom (φ : A →+* B))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[T] L ⊗[T] A).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[T] L ⊗[T] B).toRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B)) := by
    refine IsPushout.of_left ?_ ?_ hA.flip
    · convert hB.flip using 1
      · ext t; simp
      · ext t; simp
    · ext t; simp
  have := H _ _ _ (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[T] A)))
    (isPullback_SpecMap_of_isPushout _ _ _ _ sq)
    (isPullback_SpecMap_of_isPushout _ _ _ _ hA).w.symm
  exact Flat.SpecMap_iff.mp this

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp T)
    (h1 : Flat (f ≫ g)) (h2 : LocallyOfFiniteType (f ≫ g)) (h3 : LocallyOfFiniteType g)
    (hK : FlatOver f g (spMap (algebraMap T K))) (hκ : FlatOver f g (spMap (residue T))) :
    Flat f := by
  wlog hY : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) (Y.affineCover.f i ≫ g)
      (by rw [e]; infer_instance) (by rw [e]; infer_instance) inferInstance
      (hK.target sq) (hκ.target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance) (hK.source _) (hκ.source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h2
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h2 h3
  letI : Algebra T A := g.hom.toAlgebra
  letI : Algebra T B := (g ≫ f).hom.toAlgebra
  haveI : Module.Flat T B := h1
  haveI : Algebra.FiniteType T B := h2
  haveI : Algebra.FiniteType T A := h3
  haveI := Algebra.FiniteType.isNoetherianRing T A
  haveI := Algebra.FiniteType.isNoetherianRing T B
  let φ : A →ₐ[T] B := { f.hom with commutes' := fun _ => rfl }
  exact ringHom_flat K φ (FlatOver.tensor φ hK) (FlatOver.tensor φ hκ)

end FibreFlat

theorem flat_of_flat_fibres_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (X Y : Over (Sp T)) (φ : X ⟶ Y), Flat X.hom → Flat Y.hom →
      LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom →
      Flat ((Over.pullback (spMap (algebraMap T K))).map φ).left →
      Flat ((Over.pullback (spMap (IsLocalRing.residue T))).map φ).left → Flat φ.left := by
  intro T K _ _ _ _ _ _ X Y φ h1 _ h2 h3 hK hκ
  exact FibreFlat.flat_of_flatOver T K φ.left Y.hom (by rwa [Over.w]) (by rwa [Over.w]) h3
    (FibreFlat.flatOver_of_pullback φ _ hK) (FibreFlat.flatOver_of_pullback φ _ hκ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem ringHom_flat_of_injective_of_isUnit {T A B : Type*} [CommRing T] [IsDomain T] [IsBezout T]
    [CommRing A] [CommRing B] (φ : T →+* A) (ψ : A →+* B) (hψ : Function.Injective ψ)
    (h : ∀ t : T, t ≠ 0 → IsUnit (ψ (φ t))) : φ.Flat := by
  letI := φ.toAlgebra
  change Module.Flat T A
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨t, ht⟩, hta⟩
  have h1 : φ t * a = 0 := hta
  have h2 : ψ (φ t) * ψ a = 0 := by rw [← map_mul, h1, map_zero]
  have h3 : ψ a = 0 := (h t (nonZeroDivisors.ne_zero ht)).mul_right_eq_zero.mp h2
  exact hψ (by rw [h3, map_zero])

theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem flat_of_isSchemeTheoreticallyDominant_of_fractionRing (T K : Type) [CommRing T]
    [IsDomain T] [IsBezout T] [Field K] [Algebra T K] [IsFractionRing T K] {Z G : Scheme.{0}}
    (p : Z ⟶ G) [QuasiCompact p] [IsSchemeTheoreticallyDominant p] (s : G ⟶ Sp T) (z : Z ⟶ Sp K)
    (w : p ≫ s = z ≫ spMap (algebraMap T K)) : Flat s := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : G.affineOpens ↦ U)
    (iSup_affineOpens_eq_top G) fun U ↦ ?_
  have key : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top) ≫ p.app U =
      CommRingCat.ofHom (algebraMap T K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        z.appLE ⊤ (p ⁻¹ᵁ U) le_top := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, p.app_eq_appLE,
      Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
    refine (Scheme.Hom.appLE_comp_appLE p s ⊤ U (p ⁻¹ᵁ U) _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE z (spMap (algebraMap T K)) ⊤ ⊤ (p ⁻¹ᵁ U) _ _).symm)
    congr 1
  have hfl : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top).hom.Flat := by
    refine ringHom_flat_of_injective_of_isUnit (T := T) _ (p.app U).hom (p.app_injective U) ?_
    intro t ht
    have h1 : IsUnit (algebraMap T K t) :=
      IsUnit.mk0 _ (by simpa using ht)
    have h2 := h1.map ((Scheme.ΓSpecIso (.of K)).inv ≫ z.appLE ⊤ (p ⁻¹ᵁ U) le_top).hom
    have h3 := congrArg (fun φ ↦ CommRingCat.Hom.hom φ t) key
    exact h3 ▸ h2
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp hfl

theorem exists_flat_closure : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (X : Over (Sp T)) (Z : Over (Sp K)) (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj X), IsClosedImmersion i.left → ∃ (Ga : Over (Sp T)) (io : Ga ⟶ X) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧ Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io := by
  intro T K _ _ _ _ _ _ X Z i hi
  let j : Sp K ⟶ Sp T := spMap (algebraMap T K)
  have hjp : IsPreimmersion j := IsPreimmersion.of_isLocalization (nonZeroDivisors T)
  have hjf : Flat j := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors T))
  let i' : Z.left ⟶ pullback X.hom j := i.left
  have hi' : IsClosedImmersion i' := hi
  have hw : i' ≫ pullback.snd X.hom j = Z.hom := Over.w i
  let f : Z.left ⟶ X.left := i' ≫ pullback.fst X.hom j
  have hqc : QuasiCompact f := inferInstance
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  have hdom := isSchemeTheoreticallyDominant_toImage f
  have hsq : f.toImage ≫ (f.imageι ≫ X.hom) = Z.hom ≫ j := by
    rw [f.toImage_imageι_assoc, Category.assoc, pullback.condition, reassoc_of% hw]
  let Ga : Over (Sp T) := Over.mk (f.imageι ≫ X.hom)
  let io : Ga ⟶ X := Over.homMk f.imageι rfl
  let t : Z.left ⟶ pullback (f.imageι ≫ X.hom) j := pullback.lift f.toImage Z.hom hsq
  let m : pullback (f.imageι ≫ X.hom) j ⟶ pullback X.hom j :=
    pullback.map _ _ _ _ f.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩
  have hm : IsClosedImmersion m :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ m = i' := by
    apply pullback.hom_ext
    · simp [t, m, f, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [t, m, hw, pullback.lift_snd]
  have : IsClosedImmersion (t ≫ m) := htm ▸ hi'
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t m
  have hpb : IsPullback (𝟙 Z.left) t f.toImage (pullback.fst (f.imageι ≫ X.hom) j) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [t, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  refine ⟨Ga, io, (Over.isoMk (f := Z) (g := (Over.pullback j).obj Ga) (asIso t) ?_).symm,
    inferInstanceAs (IsClosedImmersion f.imageι),
    flat_of_isSchemeTheoreticallyDominant_of_fractionRing T K f.toImage _ Z.hom hsq, ?_⟩
  · exact pullback.lift_snd _ _ _
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    apply Over.OverMorphism.ext
    change i' = t ≫ _
    rw [← htm]
    congr 1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ReducedSubgroup

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]

theorem exists_grpObj_of_mono {N B : 𝒞} [GrpObj B] (ν : N ⟶ B) [Mono ν] (e : 𝟙_ 𝒞 ⟶ N)
    (m : N ⊗ N ⟶ N) (i : N ⟶ N) (he : e ≫ ν = η[B]) (hm : m ≫ ν = (ν ⊗ₘ ν) ≫ μ[B])
    (hi : i ≫ ν = ν ≫ GrpObj.inv) : ∃ _ : GrpObj N, IsMonHom ν := by
  have hl : ∀ {T : 𝒞} (a b : T ⟶ N), lift a b ≫ m ≫ ν = (a ≫ ν) * (b ≫ ν) := by
    intro T a b
    rw [hm, lift_map_assoc, Hom.mul_def]
  have hm' : m ≫ ν = (fst N N ≫ ν) * (snd N N ≫ ν) := by
    rw [← hl, lift_fst_snd, Category.id_comp]
  have he' : ∀ {T : 𝒞} (a : T ⟶ 𝟙_ 𝒞), a ≫ e ≫ ν = 1 := by
    intro T a
    rw [he, Hom.one_def, toUnit_unique a (toUnit T)]
  have hi' : i ≫ ν = ν⁻¹ := by rw [hi, Hom.inv_def]
  letI M : MonObj N :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerRight_fst_assoc,
          whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono ν]
        simp only [Category.assoc]
        conv_lhs => rw [hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, hm',
          comp_mul]
        conv_rhs => rw [hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm',
          comp_mul, comp_mul, comp_mul]
        simp [_root_.mul_assoc] }
  refine ⟨{ inv := i, left_inv := ?_, right_inv := ?_ }, ⟨he, hm⟩⟩
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl i (𝟙 N)).trans (by rw [hi', Category.id_comp, inv_mul_cancel]; exact (he' _).symm)
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl (𝟙 N) i).trans (by rw [hi', Category.id_comp, mul_inv_cancel]; exact (he' _).symm)

end Cat

section Reduced

universe u


open Scheme.IdealSheafData in
theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have : ∀ U, IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ (vanishingIdeal Z).ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover


open Scheme.IdealSheafData in
theorem vanishingIdeal_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X)
    (Z : TopologicalSpace.Closeds X) (h : Set.range g ⊆ Z) : vanishingIdeal Z ≤ g.ker := by
  refine le_ofIdeals_iff.mpr fun U a ha => ?_
  rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
  intro t ht
  have h1 : g t ∈ (vanishingIdeal Z).support := h ⟨t, rfl⟩
  have h2 := ((coe_support_inter (vanishingIdeal Z) U).le
    ⟨h1, X.basicOpen_le a ht⟩).1
  exact ((Scheme.mem_zeroLocus_iff _ _ _).mp h2 a ha ht).elim

theorem geometricallyReduced_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of k)) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩
  let 𝒰 := Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := X.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (X.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (X.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (X.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra k (X.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 := ReducedAlg.isReduced_tensor (k := k) (X.affineOpenCover.X i) K
    have h3 := (affine_isReduced_iff
      (.of (TensorProduct k (X.affineOpenCover.X i) K))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k (X.affineOpenCover.X i) K).hom
  exact IsReduced.of_openCover _ 𝒰

end Reduced

theorem range_subset_of_points {k : Type} [Field k] [IsAlgClosed k] {T B : Over (Sp k)}
    [LocallyOfFiniteType T.hom] (g : T ⟶ B) {Z : Set B.left} (hZ : IsClosed Z)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Z) : Set.range g.left ⊆ Z := by
  have := LocallyOfFiniteType.jacobsonSpace T.hom
  rintro _ ⟨t, rfl⟩
  by_contra ht
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := (g.left ⁻¹' Z)ᶜ) ⟨t, ht⟩
    (hZ.preimage g.left.continuous).isOpen_compl.isLocallyClosed
  let x' : 𝟙_ (Over (Sp k)) ⟶ T :=
    Over.homMk (pointOfClosedPoint T.hom x hxc) (pointOfClosedPoint_comp T.hom x hxc)
  refine hx (h x' ⟨IsLocalRing.closedPoint k, ?_⟩)
  exact congrArg g.left (pointOfClosedPoint_apply T.hom x hxc _)


open Scheme.IdealSheafData in
theorem exists_smooth_closed_subgroup (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k))
    [GrpObj B] (hB : LocallyOfFiniteType B.hom) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B))
    (Z : Set B.left) (hZ : IsClosed Z) (hC : ∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) :
    ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ B), IsMonHom ν ∧ IsClosedImmersion ν.left ∧
      Smooth N.hom ∧ Set.range ν.left = Z := by
  let I : B.left.IdealSheafData := vanishingIdeal ⟨Z, hZ⟩
  let N : Over (Sp k) := Over.mk (I.subschemeι ≫ B.hom)
  let ν : N ⟶ B := Over.homMk I.subschemeι rfl
  have hν : IsClosedImmersion ν.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hr : Set.range ν.left = Z := by
    change Set.range I.subschemeι = Z
    rw [range_subschemeι]
    rfl
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hred : IsReduced N.left := isReduced_subscheme_vanishingIdeal _
  have hft : LocallyOfFiniteType N.hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))
  have hgr : GeometricallyReduced N.hom := geometricallyReduced_of_perfectField N.hom
  have hnoeth : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ B),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, x ≫ g ∈ C) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    have h1 := range_subset_of_points g hZ fun x => (hC _).mp (hg x)
    have h2 : I.subschemeι.ker ≤ g.left.ker := by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker g.left ⟨Z, hZ⟩ h1
    have h3 := IsClosedImmersion.lift_fac I.subschemeι g.left h2
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι g.left h2) ?_, ?_⟩
    · change _ ≫ I.subschemeι ≫ B.hom = _
      rw [← Category.assoc, h3, Over.w]
    · ext1
      exact h3
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have : LocallyOfFiniteType (𝟙_ (Over (Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Sp k)))
  have : IsReduced (N ⊗ N).left := inferInstanceAs (IsReduced (pullback N.hom N.hom))
  have : LocallyOfFiniteType (N ⊗ N).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst N.hom N.hom ≫ N.hom))
  obtain ⟨e, he⟩ := hlift η[B] fun x => by
    rw [toUnit_unique x (toUnit _), ← Hom.one_def]
    exact C.one_mem
  obtain ⟨m, hm⟩ := hlift ((ν ⊗ₘ ν) ≫ μ[B]) fun x => by
    have : x ≫ (ν ⊗ₘ ν) ≫ μ[B] = ((x ≫ fst N N) ≫ ν) * ((x ≫ snd N N) ≫ ν) := by
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [this]
    exact C.mul_mem (hmem _) (hmem _)
  obtain ⟨i, hi⟩ := hlift (ν ≫ GrpObj.inv) fun x => by
    rw [← Category.assoc, ← Hom.inv_def]
    exact C.inv_mem (hmem _)
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨N, G, ν, hG, hν, ?_, hr⟩
  letI : GrpObj (Over.mk N.hom) := G
  exact smooth_of_grpObj N.hom

end GlobalTheory.ReducedSubgroup
end

