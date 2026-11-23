module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0073
public import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.EtaleCohomology.EtaleSheaves.Bundle0075
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0022
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0021
public import Development.EtaleCohomology.EtaleSheaves.Bundle0044
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0036
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0019
public import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DescentMapFactorsThroughStage
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut
  LateralTheory.E.LeafDescendFPPf

namespace UpperTheory.Cb.DescentMapFactorization

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {E : Scheme.{0}} (p : E ⟶ Sp R)

private def tR : LateralTheory.E.LeafDescendMapPf.D R p ⟶ (Functor.const _).obj (Sp R) where
  app S := pullback.snd _ _ ≫ incl S.unop.2.1
  naturality S T h := by
    simp only [Functor.const_obj_map, Category.comp_id]
    erw [pullback.lift_snd_assoc]
    rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.incl_incl]
    exact (Category.comp_id _).symm

private lemma tR_app (S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ) : (tR R p).app S =
    pullback.snd p (incl S.unop.2.1) ≫ incl S.unop.2.1 := rfl

end UpperTheory.Cb.DescentMapFactorization

open UpperTheory.Cb.DescentMapFactorization in
theorem UpperTheory.Cb.descent_map_factors_through_stage :
    LateralTheory.E.LeafPairRelPf.LeafFactorStage := by
  intro k _ Ω _ _ R hR C E Y c p w hp hs f hf a ha
  obtain ⟨h1, h2, h3⟩ := hp
  haveI : Nonempty (LateralTheory.E.LeafDescendMapPf.J R) := ⟨⟨R, le_rfl, hR⟩⟩
  haveI : ∀ S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ, CompactSpace ((LateralTheory.E.LeafDescendMapPf.D R p).obj S) := by
    intro S
    dsimp only [LateralTheory.E.LeafDescendMapPf.D]
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p _)
  haveI : ∀ S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ, QuasiSeparatedSpace ((LateralTheory.E.LeafDescendMapPf.D R p).obj S) := by
    intro S
    dsimp only [LateralTheory.E.LeafDescendMapPf.D]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p _)
  have hcomm : (LateralTheory.E.LeafDescendMapPf.cone R p c w hs).π ≫ tR R p = (Functor.const _).map (a ≫ f) := by
    ext S
    simp only [NatTrans.comp_app, Functor.const_map_app]
    rw [tR_app]
    simp only [pullback.lift_snd_assoc, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]
    exact ha.symm
  obtain ⟨S, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (LateralTheory.E.LeafDescendMapPf.D R p) (tR R p) f (LateralTheory.E.LeafDescendMapPf.cone R p c w hs)
    (LateralTheory.E.LeafDescendMapPf.coneIsLimit R p c w hs hR) a hcomm
  exact ⟨S.unop.1, S.unop.2.1, S.unop.2.2, g, hg2, hg1⟩

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleFinitePresentationModelExists
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut TopologicalSpace

namespace UpperTheory.Cb

private def rho (R : Type) [CommRing R] (V : (Spec (CommRingCat.of R)).Opens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom

private theorem away_rho (R : Type) [CommRing R] (f : R) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : ((show Opens (PrimeSpectrum R) from V) : Set (PrimeSpectrum R)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) :
    @IsLocalization.Away R _ f Γ(Spec (CommRingCat.of R), V) _ (rho R V).toAlgebra := by
  have hb : V = (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) := by
    rw [basicOpen_eq_of_affine]
    exact Opens.ext hV
  have h := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_of_eq_basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) (homOfLE le_top : V ⟶ ⊤) hb
  let φ : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := ((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.toAlgebra
  have h2 := (IsLocalization.isLocalization_iff_of_base_ringEquiv (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) Γ(Spec (CommRingCat.of R), V) φ.symm).1 h
  have hp : Submonoid.map φ.symm (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) = Submonoid.powers f := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (φ.symm_apply_apply f)
  rw [hp] at h2
  exact h2

private theorem loc_part {W : Type} [CommRing W] (hW : ProdACF W) (q : PrimeSpectrum W)
    (V : (Spec (CommRingCat.of W)).Opens) (hV : IsCompact (V : Set (Spec (CommRingCat.of W)))) :
    ∃ S : Submonoid Γ(Spec (CommRingCat.of W), V), (∀ s ∈ S, IsIdempotentElem s) ∧
      @IsLocalization _ _ S
        Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)),
          Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ V) _
        (Scheme.Hom.app (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))) V).hom.toAlgebra := by
  obtain ⟨e, he, hVe⟩ := UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF hW V hV
  obtain ⟨T, hT, hTL⟩ := UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  letI : Algebra W Γ(Spec (CommRingCat.of W), V) := (rho W V).toAlgebra
  letI : Algebra (Localization.AtPrime q.asIdeal) Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) :=
    (rho _ (j ⁻¹ᵁ V)).toAlgebra
  haveI : IsLocalization.Away e Γ(Spec (CommRingCat.of W), V) := away_rho W e V hVe
  haveI : IsLocalization.Away (algebraMap W (Localization.AtPrime q.asIdeal) e)
      Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) := by
    refine away_rho (Localization.AtPrime q.asIdeal) (algebraMap W (Localization.AtPrime q.asIdeal) e) (j ⁻¹ᵁ V) ?_
    ext x
    have := Set.ext_iff.1 hVe (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal)) x)
    exact this
  refine UpperTheory.exists_idempotent_submonoid_isLocalization_away (L := Localization.AtPrime q.asIdeal) e he T (fun s hs => (hT s hs).1) (j.app V).hom ?_
  intro r
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have key : (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
      (Spec (CommRingCat.of W)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ j.app V =
      CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime q.asIdeal))).inv ≫
        (Spec (CommRingCat.of (Localization.AtPrime q.asIdeal))).presheaf.map (homOfLE le_top : j ⁻¹ᵁ V ⟶ ⊤).op := by
    rw [j.naturality, reassoc_of% h1]
    rfl
  exact congr($key r)

private theorem sec_part {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hle : f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U)) :
    Function.Injective (f.toNormalization.appLE _ _ hle).hom ∧
    ∀ b, b ∈ (f.toNormalization.appLE _ _ hle).hom.range ↔ (f.app U).hom.IsIntegralElem b := by
  letI := (f.app U).hom.toAlgebra
  have h := f.normalizationObjIso_hom_val hU
  have h2 : f.toNormalization.appLE _ _ hle = _ := h.symm
  rw [h2]
  have hb := ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom
  constructor
  · intro x y hxy
    exact hb.1 (Subtype.ext hxy)
  · intro b
    constructor
    · rintro ⟨x, rfl⟩
      exact ((f.normalizationObjIso hU).hom.hom x).2
    · intro hbi
      obtain ⟨x, hx⟩ := hb.2 ⟨b, hbi⟩
      exact ⟨x, congrArg Subtype.val hx⟩

private theorem hleN {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (U : Y.Opens) :
    f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) := by
  have h : f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  exact h.ge

private theorem appLE_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

end UpperTheory.Cb

theorem UpperTheory.Cb.etale_finite_presentation_model_exists :
    LateralTheory.E.BuildCut.LimInt → LateralTheory.E.t_E2Cut.Cont → LateralTheory.E.t_E2Cut.MV → LateralTheory.E.SysFMPf.FMex := by
  intro _ _ _ P _ _ W _ w hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  let m := GlobalTheory.normalizationLift (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)
  have e1 : j ≫ w.toNormalization = (j ≫ w).toNormalization ≫ m :=
    (GlobalTheory.toNormalization_normalizationLift _ _ _ _ _).symm
  have e2 : m ≫ w.fromNormalization = (j ≫ w).fromNormalization :=
    (GlobalTheory.normalizationLift_comp (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)).trans
      (Category.comp_id _)
  have hmi : IsIntegralHom m := GlobalTheory.isIntegralHom_normalizationLift _ _ _ _ _
  obtain ⟨hmono, hflat⟩ := UpperTheory.mono_flat_of_affine_appLE_flat_epi w.fromNormalization (j ≫ w).fromNormalization m e2 (fun U hU hle => by
    obtain ⟨S, hS, hL⟩ := loc_part hW q (w ⁻¹ᵁ U) (w.isCompact_preimage hU.isCompact)
    obtain ⟨ht, hr⟩ := sec_part w hU (hleN w U)
    obtain ⟨ht', hr'⟩ := sec_part (j ≫ w) hU (hleN (j ≫ w) U)
    have key : w.toNormalization.appLE _ _ (hleN w U) ≫ j.app (w ⁻¹ᵁ U) =
        m.appLE _ _ hle ≫ (j ≫ w).toNormalization.appLE _ _ (hleN (j ≫ w) U) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq e1 _ _ _
    refine UpperTheory.integralClosure_range_isLocalization_idempotent (w.app U).hom (j.app (w ⁻¹ᵁ U)).hom _ _ _ ht ht' hr (fun b => (hr' b).trans Iff.rfl) ?_ S hS hL
    intro c
    exact congr($key c))
  exact ⟨m, e1, e2, hmono, hflat, inferInstance⟩

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExtensionByZeroOfZariskiQuasiFiniteFactorization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGeoVCut

namespace UpperTheory.Cb.ZariskiExtensionByZero

private theorem stage (k : Type) [Field k] [PerfectField k] {T D : Scheme.{0}} (t : T ⟶ Sp k)
    [LocallyOfFiniteType t] (f : D ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyQuasiFinite f] [IsIntegral D] :
    ∃ (Y : Scheme.{0}) (g : Y ⟶ T) (j : D ⟶ Y), IsFinite g ∧ IsOpenImmersion j ∧ j ≫ g = f ∧
      IsIntegral Y ∧ Dense (Set.range j) :=
  ⟨f.normalization, f.fromNormalization, f.toNormalization, UpperTheory.isFinite_fromNormalization_of_perfectField k t f, inferInstance,
    f.toNormalization_fromNormalization, inferInstance,
    (inferInstance : IsDominant f.toNormalization).denseRange⟩

private theorem pull_of {B D Y C S T : Scheme.{0}} (j : D ⟶ Y) [IsOpenImmersion j] (π : Y ⟶ B)
    (ι : S ⟶ B) [Mono ι] (q : D ⟶ S) (w : j ≫ π = q ≫ ι) (v : C ⟶ D) (c : C ⟶ T) (s : T ⟶ S)
    (hP : IsPullback v c q s) (h : ∀ y, π y ∈ Set.range (s ≫ ι) → y ∈ Set.range j) :
    IsPullback (v ≫ j) c π (s ≫ ι) := by
  have hw : (v ≫ j) ≫ π = c ≫ s ≫ ι := by
    rw [Category.assoc, w, ← Category.assoc, hP.w, Category.assoc]
  have hr : ∀ z : PullbackCone π (s ≫ ι), Set.range z.fst ⊆ Set.range j := by
    rintro z _ ⟨x, rfl⟩
    refine h _ ⟨z.snd x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, z.condition]
  have hl : ∀ z : PullbackCone π (s ≫ ι),
      IsOpenImmersion.lift j z.fst (hr z) ≫ q = z.snd ≫ s := by
    intro z
    rw [← cancel_mono ι, Category.assoc, ← w, IsOpenImmersion.lift_fac_assoc, z.condition,
      Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun z => hP.lift (IsOpenImmersion.lift j z.fst (hr z)) z.snd (hl z))
    (fun z => ?_) (fun z => ?_) (fun z m h1 h2 => ?_)⟩⟩
  · rw [IsPullback.lift_fst_assoc, IsOpenImmersion.lift_fac]
  · rw [IsPullback.lift_snd]
  · refine hP.hom_ext ?_ ?_
    · rw [IsPullback.lift_fst, ← cancel_mono j, IsOpenImmersion.lift_fac, Category.assoc]
      exact h1
    · rw [IsPullback.lift_snd]; exact h2

private theorem smooth_of {B D Y S : Scheme.{0}} (j : D ⟶ Y) [IsOpenImmersion j] (π : Y ⟶ B)
    (ι : S ⟶ B) [IsOpenImmersion ι] (q : D ⟶ S) [Smooth q] (w : j ≫ π = q ≫ ι) (V : B.Opens)
    (h : ∀ y, π y ∈ V → y ∈ Set.range j) : Smooth (π ∣_ V) := by
  have hr : Set.range (π ⁻¹ᵁ V).ι ⊆ Set.range j := by
    rw [Scheme.Opens.range_ι]
    intro y hy
    exact h y hy
  have e : (π ⁻¹ᵁ V).ι ≫ π = IsOpenImmersion.lift j _ hr ≫ q ≫ ι := by
    rw [← w, ← Category.assoc, IsOpenImmersion.lift_fac]
  have hs : Smooth ((π ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι, e]
    infer_instance
  haveI hloc : IsZariskiLocalAtTarget @Smooth.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  haveI : MorphismProperty.RespectsIso @Smooth.{0} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  haveI : MorphismProperty.HasOfPostcompProperty @Smooth.{0} @IsOpenImmersion.{0} :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict _
      (fun f U hf => IsZariskiLocalAtTarget.restrict hf U)
  exact MorphismProperty.of_postcomp (W := @Smooth.{0}) (W' := @IsOpenImmersion.{0}) _ V.ι
    inferInstance hs

end UpperTheory.Cb.ZariskiExtensionByZero

open UpperTheory.Cb.ZariskiExtensionByZero in
theorem UpperTheory.Cb.extension_by_zero_of_zariski_quasi_finite_factorization :
    LateralTheory.E.LeafGeoVV2Cut.LeafExtendZMT := by
  intro k _ _ X p _ Ω _ _ R B b _ ι _ hιb C0 C1 C2 c0 γ1 γ2 e hc0 hc1 hc2 he D0 D1 D2 q d1 d2 f
    v0 v1 v2 hf hs0 hq0 hsm0 hs1 hq1 hsm1 hs2 hq2 hsm2 hI0 hI1 hI2 hlqf hd1 hd2 hP0 hP1 hP2
    hc10 hc21 hve
  haveI hsq0 : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  haveI hsq1 : Smooth (d1 ≫ q) := SmoothOfRelativeDimension.smooth 1 _
  haveI hsq2 : Smooth (d2 ≫ d1 ≫ q) := SmoothOfRelativeDimension.smooth 1 _
  have hcond : (q ≫ ι) ≫ b = f ≫ p := by rw [Category.assoc, hιb, hf]
  let F0 : D0 ⟶ pullback b p := pullback.lift (q ≫ ι) f hcond
  have hF0f : F0 ≫ pullback.fst b p = q ≫ ι := pullback.lift_fst _ _ _
  have hF0s : F0 ≫ pullback.snd b p = f := pullback.lift_snd _ _ _
  have hF0m : F0 = pullback.lift q f hf.symm ≫
      pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k R))) p b p ι (𝟙 X) (𝟙 _)
        (by rw [Category.comp_id, hιb]) (by simp) := by
    apply pullback.hom_ext
    · rw [hF0f, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [hF0s, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  haveI : LocallyQuasiFinite F0 := by rw [hF0m]; infer_instance
  haveI : QuasiCompact ι := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) ι b inferInstance (by rw [hιb]; infer_instance)
  haveI : LocallyOfFiniteType F0 := by
    have : LocallyOfFiniteType (F0 ≫ pullback.fst b p) := by rw [hF0f]; infer_instance
    exact locallyOfFiniteType_of_comp F0 (pullback.fst b p)
  haveI : QuasiCompact F0 := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) F0 (pullback.fst b p) inferInstance (by rw [hF0f]; infer_instance)
  haveI : IsSeparated F0 := MorphismProperty.of_postcomp (W := @IsSeparated)
    (W' := ⊤) F0 (pullback.fst b p) trivial (by rw [hF0f]; infer_instance)
  obtain ⟨Y0, g0, j0, hg0, hj0, hjg0, hY0, hdn0⟩ := stage k (pullback.fst b p ≫ b) F0
  obtain ⟨π, hπ⟩ : ∃ π' : Y0 ⟶ B, π' = g0 ≫ pullback.fst b p := ⟨_, rfl⟩
  haveI : IsProper π := by rw [hπ]; infer_instance
  have hw0 : j0 ≫ π = q ≫ ι := by rw [hπ, ← Category.assoc, hjg0, hF0f]
  haveI : LocallyOfFiniteType d1 := locallyOfFiniteType_of_comp d1 q
  have hF1 : (d1 ≫ j0) ≫ π = (d1 ≫ q) ≫ ι := by rw [Category.assoc, hw0, Category.assoc]
  haveI : QuasiCompact (d1 ≫ j0) := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) _ π inferInstance (by rw [hF1]; infer_instance)
  haveI : IsSeparated (d1 ≫ j0) := MorphismProperty.of_postcomp (W := @IsSeparated)
    (W' := ⊤) _ π trivial (by rw [hF1]; infer_instance)
  obtain ⟨Y1, g1, j1, hg1, hj1, hjg1, hY1, hdn1⟩ := stage k (π ≫ b) (d1 ≫ j0)
  have hw1 : j1 ≫ g1 ≫ π = (d1 ≫ q) ≫ ι := by rw [← Category.assoc, hjg1, hF1]
  haveI : LocallyOfFiniteType d2 := locallyOfFiniteType_of_comp d2 (d1 ≫ q)
  have hF2 : (d2 ≫ j1) ≫ g1 ≫ π = (d2 ≫ d1 ≫ q) ≫ ι := by
    rw [Category.assoc, hw1]
    simp only [Category.assoc]
  haveI : QuasiCompact (d2 ≫ j1) := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) _ (g1 ≫ π) inferInstance (by rw [hF2]; infer_instance)
  haveI : IsSeparated (d2 ≫ j1) := MorphismProperty.of_postcomp (W := @IsSeparated)
    (W' := ⊤) _ (g1 ≫ π) trivial (by rw [hF2]; infer_instance)
  obtain ⟨Y2, g2, j2, hg2, hj2, hjg2, hY2, hdn2⟩ := stage k ((g1 ≫ π) ≫ b) (d2 ≫ j1)
  have hw2 : j2 ≫ g2 ≫ g1 ≫ π = (d2 ≫ d1 ≫ q) ≫ ι := by rw [← Category.assoc, hjg2, hF2]
  haveI := hc0.2.1
  haveI := hc1.2.1
  haveI := hc2.2.1
  have hinj : Function.Injective (algebraMap R Ω) := fun x y hxy => Subtype.ext hxy
  have hpl0 := UpperTheory.mem_range_of_proper_generic_fibre_separated R Ω hinj ι π j0 hdn0 q hw0 c0 v0 hP0
  have hpl1 := UpperTheory.mem_range_of_proper_generic_fibre_separated R Ω hinj ι (g1 ≫ π) j1 hdn1 (d1 ≫ q) hw1 (γ1 ≫ c0) v1 hP1
  have hpl2 := UpperTheory.mem_range_of_proper_generic_fibre_separated R Ω hinj ι (g2 ≫ g1 ≫ π) j2 hdn2 (d2 ≫ d1 ≫ q) hw2
    (γ2 ≫ γ1 ≫ c0) v2 hP2
  have hZ : ∀ {Y W : Scheme} (π' : Y ⟶ B) [IsProper π'] (j : W ⟶ Y) [IsOpenImmersion j],
      IsClosed (π' '' (Set.range j)ᶜ) := fun π' _ j _ =>
    π'.isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl
  let V : B.Opens := ⟨(π '' (Set.range j0)ᶜ ∪ (g1 ≫ π) '' (Set.range j1)ᶜ ∪
      (g2 ≫ g1 ≫ π) '' (Set.range j2)ᶜ)ᶜ,
    (((hZ π j0).union (hZ _ j1)).union (hZ _ j2)).isOpen_compl⟩
  have hV0 : ∀ y, π y ∈ V → y ∈ Set.range j0 := by
    intro y hy
    by_contra hn
    exact hy (Or.inl (Or.inl ⟨y, hn, rfl⟩))
  have hV1 : ∀ y, (g1 ≫ π) y ∈ V → y ∈ Set.range j1 := by
    intro y hy
    by_contra hn
    exact hy (Or.inl (Or.inr ⟨y, hn, rfl⟩))
  have hV2 : ∀ y, (g2 ≫ g1 ≫ π) y ∈ V → y ∈ Set.range j2 := by
    intro y hy
    by_contra hn
    exact hy (Or.inr ⟨y, hn, rfl⟩)
  have hVr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ⊆ (V : Set B) := by
    intro x hx hmem
    rcases hmem with (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩
    · exact hz (hpl0 z hx)
    · exact hz (hpl1 z hx)
    · exact hz (hpl2 z hx)
  refine ⟨Y0, Y1, Y2, π, g1, g2, g0 ≫ pullback.snd b p, V, v0 ≫ j0, v1 ≫ j1, v2 ≫ j2, hVr,
    by unfold SmP; exact ⟨inferInstance, smooth_of j0 π ι q hw0 V hV0⟩,
    by unfold SmP; exact ⟨inferInstance, smooth_of j1 (g1 ≫ π) ι (d1 ≫ q) hw1 V hV1⟩,
    by unfold SmP; exact ⟨inferInstance, smooth_of j2 (g2 ≫ g1 ≫ π) ι _ hw2 V hV2⟩,
    inferInstance, inferInstance, UpperTheory.topologicalKrullDim_le_of_isOpenImmersion_integral k (π ≫ b) j0,
    pull_of j0 π ι q hw0 v0 c0 _ hP0 hpl0, pull_of j1 _ ι _ hw1 v1 _ _ hP1 hpl1,
    pull_of j2 _ ι _ hw2 v2 _ _ hP2 hpl2, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hc10, Category.assoc, Category.assoc, hjg1]
  · rw [← Category.assoc, hc21, Category.assoc, Category.assoc, hjg2]
  · rw [Category.assoc, ← Category.assoc j0, hjg0, hF0s, hve]

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.StrictlyHenselianLocalOfNegligibleDegree
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open LateralTheory.E.E4 LateralTheory.E.StrictHenselianNeighbourhood

namespace UpperTheory.Cb

private theorem factor_later {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (hP : IsPtNb U x Ω s D c V a l e t)
    (j : J) (E : Type) [CommRing E] [Algebra (D.obj j) E] [Algebra.Etale (D.obj j) E]
    (ψ : E →+* Ω)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E)) = l j) :
    ∃ (k : J) (g : j ⟶ k) (φ : E →+* D.obj k), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
      l k ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) := by
  obtain ⟨-, he, hl, hcomp, -, hlc, hcof, heq⟩ := hP
  let π : Sp E ⟶ Sp (D.obj j) := Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E))
  haveI hπ : Etale π := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  haveI : IsIso (e j) := he j
  let q : Sp E ⟶ (V j).left := π ≫ e j
  let W : B.Etale := Scheme.Etale.mk (q ≫ (V j).hom)
  let bj : W ⟶ V j := MorphismProperty.Over.homMk q rfl
  have hpt : Spec.map (CommRingCat.ofHom ψ) ≫ q = l j ≫ e j := by
    rw [← hψ]; simp [q, π]
  have hs : Spec.map (CommRingCat.ofHom ψ) ≫ q ≫ (a j).left = s := by
    rw [reassoc_of% hpt, hl]
  obtain ⟨k, g, hg, hgl⟩ := hcof W (bj ≫ a j) (Spec.map (CommRingCat.ofHom ψ)) hs
  obtain ⟨g', hg', hgl'⟩ : ∃ g' : (V k).left ⟶ Sp E, g' ≫ q ≫ (a j).left = (a k).left ∧
      l k ≫ e k ≫ g' = Spec.map (CommRingCat.ofHom ψ) := ⟨g, hg, hgl⟩
  clear hg hgl g hs
  let m := IsFiltered.max j k
  let u : j ⟶ m := IsFiltered.leftToMax j k
  let v : k ⟶ m := IsFiltered.rightToMax j k
  haveI : IsIso (e m) := he m
  let g1 : (V m).left ⟶ (V j).left :=
    inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map u).hom) ≫ e j
  let g2 : (V m).left ⟶ (V j).left :=
    inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map v).hom) ≫ e k ≫ g' ≫ q
  have h1 : g1 ≫ (a j).left = (a m).left := by
    simp only [g1, Category.assoc]; rw [hcomp j m u]; simp
  have h2 : g2 ≫ (a j).left = (a m).left := by
    simp only [g2, Category.assoc]; rw [hg', hcomp k m v]; simp
  have h3 : l m ≫ e m ≫ g1 = l m ≫ e m ≫ g2 := by
    simp only [g1, g2, IsIso.hom_inv_id_assoc]
    rw [reassoc_of% (hlc j m u), reassoc_of% (hlc k m v), reassoc_of% hgl', hpt]
  obtain ⟨n, w, hw⟩ := heq (V j) (a j) m g1 g2 h1 h2 h3
  simp only [g1, g2, IsIso.hom_inv_id_assoc] at hw
  let h : Sp (D.obj n) ⟶ Sp E :=
    Spec.map (CommRingCat.ofHom (D.map w).hom) ≫ Spec.map (CommRingCat.ofHom (D.map v).hom) ≫
      e k ≫ g'
  have hh : h ≫ π = Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) := by
    rw [← cancel_mono (e j)]
    have : Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) =
        Spec.map (CommRingCat.ofHom (D.map w).hom) ≫ Spec.map (CommRingCat.ofHom (D.map u).hom) := by
      rw [← Spec.map_comp]; simp
    rw [this]
    simp only [Category.assoc]
    rw [hw]
    simp [h, q]
  refine ⟨n, u ≫ w, (Spec.preimage h).hom, ?_, ?_⟩
  · have h4 : Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E) ≫ Spec.preimage h) =
        Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) := by
      rw [Spec.map_comp, Spec.map_preimage]; exact hh
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h4)
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    simp only [h]
    rw [reassoc_of% (hlc m n w), reassoc_of% (hlc k m v), hgl']

end UpperTheory.Cb

theorem UpperTheory.Cb.strictlyHenselianLocal_of_negligibleDegree :
    LateralTheory.E.LeafDegCut.LeafNeg → LateralTheory.E.StrictHenselianNeighbourhood.LeafSHHens := by
  intro _ B U x Ω _ _ s J _ _ D c hc V a l e t hP _
  let ρ : ∀ j, D.obj j ⟶ CommRingCat.of Ω := fun j => Spec.preimage (l j)
  have hρ : ∀ j, Spec.map (ρ j) = l j := fun j => Spec.map_preimage _
  have hlc := hP.2.2.2.2.2.1
  have hw : ∀ (j k : J) (f : j ⟶ k), D.map f ≫ ρ k = ρ j := by
    intro j k f
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, hρ, ← hlc j k f]
    rfl
  let cc : Cocone D :=
    { pt := CommRingCat.of Ω
      ι := { app := ρ, naturality := fun j k f => by simpa using hw j k f } }
  let ω : c.pt →+* Ω := (hc.desc cc).hom
  have hω : ∀ j, ω.comp (c.ι.app j).hom = (ρ j).hom := fun j =>
    congrArg CommRingCat.Hom.hom (hc.fac cc j)
  refine LateralTheory.E.LeafSHSysPf.SHofCof D c hc ⟨Ω, inferInstance, inferInstance, ω, ?_⟩
  intro j E _ _ _ ψ hψ
  obtain ⟨k, g, φ, h1, h2⟩ := factor_later U x Ω s D c V a l e t hP j E ψ (by
    rw [← Spec.map_comp, ← hρ j]
    congr 1
    apply CommRingCat.hom_ext
    rw [hω j] at hψ
    exact hψ)
  refine ⟨k, g, φ, h1, ?_⟩
  rw [← RingHom.comp_assoc, hω k]
  have h3 : CommRingCat.ofHom φ ≫ ρ k = CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ]
    exact h2
  exact congrArg CommRingCat.Hom.hom h3
end
end

