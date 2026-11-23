module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0012

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartB
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial IsLocalRing

noncomputable def jacSpanAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Submodule ℂ (σ → ℂ) :=
  Submodule.span ℂ ((fun h : MvPolynomial σ ℂ => fun j => eval z (pderiv j h)) '' (I : Set _))

theorem locAt_isLocalRing_isNoetherian {σ : Type} [Finite σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    IsLocalRing (locAt I z) ∧ IsNoetherianRing (locAt I z) := by
  haveI := Fintype.ofFinite σ
  have hle : I ≤ ptIdealOf z := fun h hh => by
    show h ∈ RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)
    exact hz h hh
  have hne : Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I ≠ ⊤ := by
    intro htop
    have h1 : Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)))
        (ptIdealOf z) = ⊤ := top_unique (htop ▸ Ideal.map_mono hle)
    rw [Localization.AtPrime.map_eq_maximalIdeal] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  haveI : Nontrivial (locAt I z) := Ideal.Quotient.nontrivial_iff.2 hne
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, inferInstance⟩

theorem grad_renC {σ : Type} [Fintype σ] (z : σ → ℂ) (h : MvPolynomial σ ℂ) :
    grad (renPt z) (renC σ h) = fun j => eval z (pderiv ((Fintype.equivFin σ).symm j) h) := by
  funext j
  simp only [grad, renC, renameEquiv_apply]
  conv_lhs => rw [← Equiv.apply_symm_apply (Fintype.equivFin σ) j]
  rw [pderiv_rename (Equiv.injective _), eval_rename]
  have hc : renPt z ∘ (Fintype.equivFin σ) = z := by
    funext i
    simp [renPt]
  rw [hc]

theorem finrank_jacSpanAt_eq {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    Module.finrank ℂ (jacSpanAt I z) =
      Module.finrank ℂ (jacSpan (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) := by
  let L : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
  have hset : grad (renPt z) '' ((I.map (renR σ : MvPolynomial σ ℂ →+* MvPolynomial (Fin (Fintype.card σ)) ℂ) :
      Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ)) : Set (MvPolynomial (Fin (Fintype.card σ)) ℂ)) =
      (L : (σ → ℂ) →ₗ[ℂ] _) '' ((fun h : MvPolynomial σ ℂ => fun j => eval z (pderiv j h)) '' (I : Set _)) := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨h, hh, rfl⟩ := (Ideal.mem_map_of_equiv (renR σ) q).1 hq
      refine ⟨_, ⟨h, hh, rfl⟩, ?_⟩
      funext j
      rw [show (renR σ) h = renC σ h from rfl, grad_renC]
      rfl
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨renR σ h, Ideal.mem_map_of_mem _ hh, ?_⟩
      funext j
      rw [show (renR σ) h = renC σ h from rfl, grad_renC]
      rfl
  unfold jacSpan jacSpanAt
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_map_eq L _).symm

theorem finrank_cotangentSpace_locAt {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) [IsLocalRing (locAt I z)] :
    Module.finrank (ResidueField (locAt I z)) (CotangentSpace (locAt I z))
      + Module.finrank ℂ (jacSpanAt I z) = Fintype.card σ := by
  haveI : IsNoetherianRing (locAt I z) := inferInstance
  haveI : Nontrivial (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    (locAtEquiv I z).symm.toEquiv.nontrivial
  haveI : IsLocalRing (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    IsLocalRing.of_surjective' (locAtEquiv I z).toRingHom (locAtEquiv I z).surjective
  haveI : IsNoetherianRing (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    isNoetherianRing_of_ringEquiv _ (locAtEquiv I z)
  rw [finrank_cotangentSpace_eq_of_ringEquiv (locAtEquiv I z), finrank_jacSpanAt_eq,
    finrank_cotangentSpace_locRing]

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsA
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem mem_nonZeroDivisors_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hb : Function.Bijective φ) {a : R} (ha : a ∈ nonZeroDivisors R) : φ a ∈ nonZeroDivisors S := by
  have key : ∀ x : S, x * φ a = 0 → x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hb.2 x
    have hz : z * a = 0 := hb.1 (by rw [map_mul, map_zero]; exact hx)
    rw [(mem_nonZeroDivisors_iff.mp ha).2 z hz, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

theorem isAffineOpen_of_iso {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) : IsAffineOpen V :=
  IsAffine.of_isIso e.hom

theorem sec_mem_nonZeroDivisors {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) {a : A} (ha : a ∈ nonZeroDivisors A) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso A).inv a)) ∈ nonZeroDivisors Γ(W, V) := by
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  have hb : Function.Bijective ((V.topIso.hom.hom).comp ((e.hom.appTop).hom.comp
      (Scheme.ΓSpecIso A).inv.hom)) :=
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).comp
      ((ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv))
  exact mem_nonZeroDivisors_of_bijective _ hb ha

theorem sec_algebraMap_of_iso {X W : Scheme.{0}} (π : W ⟶ X) (U : X.affineOpens) (V : W.Opens)
    (hV : V ≤ π ⁻¹ᵁ U.1) (A : Type) [CommRing A] [Algebra Γ(X, U.1) A]
    (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) ≫ U.2.fromSpec = V.ι ≫ π)
    (r : Γ(X, U.1)) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r))) = π.appLE _ V hV r := by
  have hVa := isAffineOpen_of_iso V e
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hVa hV
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Mono U.2.fromSpec := IsOpenImmersion.mono _
  have h3 : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) =
      hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV) := by
    rw [← cancel_mono U.2.fromSpec, Category.assoc, he, Category.assoc, h1, ← Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec]
  have n1 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
      ((Scheme.ΓSpecIso _).inv r) = (Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  have n2 : (Spec.map (π.appLE _ V hV)).appTop ((Scheme.ΓSpecIso _).inv r) =
      (Scheme.ΓSpecIso _).inv (π.appLE _ V hV r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have n3 : ∀ x : Γ(W, V), hVa.isoSpec.hom.appTop ((Scheme.ΓSpecIso _).inv x) = V.topIso.inv x := by
    intro x
    rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, Iso.inv_hom_id, CommRingCat.id_apply]
  calc V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r)))
      = V.topIso.hom ((e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n1]
    _ = V.topIso.hom ((hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV)).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by rw [h3]; rfl
    _ = π.appLE _ V hV r := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [n2, n3]
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem germ_mem_nonZeroDivisors {W : Scheme.{0}} {V : W.Opens} (hV : IsAffineOpen V) {a : Γ(W, V)}
    (ha : a ∈ nonZeroDivisors Γ(W, V)) (w : W) (hw : w ∈ V) :
    W.presheaf.germ V w hw a ∈ nonZeroDivisors (W.presheaf.stalk w) := by
  let := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨w, hw⟩
  have := hV.isLocalization_stalk ⟨w, hw⟩
  have h := IsLocalization.map_nonZeroDivisors_le (hV.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl
    (W.presheaf.stalk w) (Submonoid.mem_map_of_mem (algebraMap Γ(W, V) (W.presheaf.stalk w)) ha)
  exact h

theorem res_mem_nonZeroDivisors {W : Scheme.{0}} {V O : W.Opens} (h : O ≤ V) (hV : IsAffineOpen V)
    {a : Γ(W, V)} (ha : a ∈ nonZeroDivisors Γ(W, V)) :
    W.presheaf.map (homOfLE h).op a ∈ nonZeroDivisors Γ(W, O) := by
  have key : ∀ x : Γ(W, O), x * W.presheaf.map (homOfLE h).op a = 0 → x = 0 := by
    intro x hx
    refine TopCat.Presheaf.section_ext W.sheaf O x 0 (fun w hw => ?_)
    have hg := germ_mem_nonZeroDivisors hV ha w (h hw)
    have h1 : W.presheaf.germ O w hw x * W.presheaf.germ V w (h hw) a = 0 := by
      rw [← W.presheaf.germ_res_apply (homOfLE h) w hw a, ← map_mul, hx, map_zero]
    change W.presheaf.germ O w hw x = W.presheaf.germ O w hw 0
    rw [(mem_nonZeroDivisors_iff.mp hg).2 _ h1, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC
section
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

theorem sncAt_of_not_mem {Y : Scheme.{0}} (B : TopologicalSpace.Closeds Y) (y : Y)
    (hy : y ∉ (B : Set Y)) (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) :
    FinalTheorems.SncAt (Scheme.IdealSheafData.vanishingIdeal B) y := by
  refine ⟨hreg, ?_⟩
  have hfg : (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  let r : Fin s.card → Y.presheaf.stalk y := fun i => (s.equivFin.symm i).1
  have hr : Set.range r = (s : Set _) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hz
      exact ⟨s.equivFin ⟨z, hz⟩, by simp [r]⟩
  choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)
  let S : Set Y := (⋂ i, (O i : Set Y)) ∩ (B : Set Y)ᶜ
  have hSo : IsOpen S := (isOpen_iInter_of_finite fun i => (O i).2).inter B.2.isOpen_compl
  have hyS : y ∈ S := ⟨Set.mem_iInter.2 hO, hy⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyS hSo
  have hle : ∀ i, V ≤ O i := fun i z hz => Set.mem_iInter.1 (hVS hz).1 i
  refine ⟨⟨V, hV⟩, hyV, s.card, fun i => Y.presheaf.map (homOfLE (hle i)).op (t i), ∅, ⟨?_, ?_⟩, ?_⟩
  · have : (fun i => Y.presheaf.germ V y hyV (Y.presheaf.map (homOfLE (hle i)).op (t i))) = r := by
      funext i
      rw [TopCat.Presheaf.germ_res_apply]
      exact ht i
    rw [this, hr]
    exact hspan
  · rw [hs]
    exact hreg.spanFinrank_maximalIdeal
  · rw [Finset.prod_empty, Ideal.span_singleton_one, Scheme.IdealSheafData.vanishingIdeal_ideal]
    refine (Ideal.eq_top_iff_one _).2 ((PrimeSpectrum.mem_vanishingIdeal _ _).2 fun p hp => ?_)
    have hpV : hV.fromSpec p ∈ (V : Set Y) := hV.range_fromSpec ▸ ⟨p, rfl⟩
    exact ((hVS hpV).2 hp).elim

theorem isIso_morphismRestrict_of_le {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    ext x
    simp only [Scheme.Hom.coe_image, Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι, SetLike.mem_coe, Set.mem_inter_iff]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, h hx⟩⟩
  have h1 : IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U _ ≪≫ morphismRestrictEq f e)).1 h1

end

end ReciprocityTheory.AnForm.R
end

