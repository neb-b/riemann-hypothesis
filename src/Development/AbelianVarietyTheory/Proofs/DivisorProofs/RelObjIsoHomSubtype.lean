module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite

noncomputable section

namespace GlobalTheory.RelativeSpectrum

structure QCohSub {X Y : Scheme.{0}} (f : X ⟶ Y) (F : ∀ V : Y.Opens, Subring Γ(X, f ⁻¹ᵁ V)) : Prop where
  app_mem : ∀ V : Y.Opens, IsAffineOpen V → ∀ a : Γ(Y, V), (f.app V).hom a ∈ F V
  res_mem : ∀ (V V' : Y.Opens) (hle : V' ≤ V), IsAffineOpen V → IsAffineOpen V' → ∀ x ∈ F V,
    (X.presheaf.map (homOfLE (f.preimage_mono hle)).op).hom x ∈ F V'
  loc : ∀ V : Y.Opens, IsAffineOpen V → ∀ (r : Γ(Y, V)) (x : Γ(X, f ⁻¹ᵁ Y.basicOpen r)),
    x ∈ F (Y.basicOpen r) →
    ∃ (k : ℕ) (y : Γ(X, f ⁻¹ᵁ V)), y ∈ F V ∧
      (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom y =
        (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom ((f.app V).hom r) ^ k * x

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {F : ∀ V : Y.Opens, Subring Γ(X, f ⁻¹ᵁ V)}

def diagram (H : QCohSub f F) : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := .of (F U.unop.1)
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.unop.le))).op).hom.restrict
      _ _ fun x hx ↦ H.res_mem _ _ (toOpens_mono i.unop.le) V.unop.2 U.unop.2 x hx)
  map_id U := by
    ext x
    change ((X.presheaf.map (𝟙 _)).hom x.1) = x.1
    simp
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono (toOpens_mono j.unop.le))
      (f.preimage_mono (toOpens_mono i.unop.le)), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

def diagramMap (H : QCohSub f F) : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ diagram H where
  app U := CommRingCat.ofHom ((f.app U.unop.1).hom.codRestrict (F U.unop.1) (H.app_mem _ U.unop.2))
  naturality {U V} i := by
    ext x
    exact Subtype.ext congr($(f.naturality ((toOpensFunctor Y).op.map i)) x)

variable [QuasiCompact f] [QuasiSeparated f]

lemma coequifibered (H : QCohSub f F) : (diagramMap H).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have hl : IsLocalization.Away ((f.app U.1).hom r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  let := ((diagram H).map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · have h1 : IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r) :=
      Y.toRingedSpace.isUnit_res_basicOpen r
    have h2 := h1.map ((diagramMap H).app (.op (U.basicOpen r))).hom
    convert h2 using 1
    exact congr($((diagramMap H).naturality (homOfLE (U.basicOpen_le r)).op) r).symm
  · intro s
    obtain ⟨k, y, hy, e⟩ := H.loc U.1 U.2 r s.1 s.2
    refine ⟨k, ⟨y, hy⟩, Subtype.ext ?_⟩
    exact (mul_comm _ _).trans e.symm
  · intro a b hab
    have hab' : algebraMap Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) a.1 =
        algebraMap Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) b.1 := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq ((f.app U.1).hom r) hab'
    exact ⟨n, Subtype.ext hn⟩

def glueData (H : QCohSub f F) := relativeGluingData (coequifibered H)

instance (H : QCohSub f F) : ((glueData H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def relSpec (H : QCohSub f F) : Scheme := (glueData H).glued

def relCover (H : QCohSub f F) : (relSpec H).OpenCover := (glueData H).cover


lemma isOpenImmersion_relCover (H : QCohSub f F) (U : Y.affineOpens) :
    IsOpenImmersion ((relCover H).f U) :=
  (relCover H).map_prop U

attribute [local instance] isOpenImmersion_relCover

def toRel (H : QCohSub f F) : X ⟶ relSpec H :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U ↦
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ (relCover H).f U)
    fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    have h2 : (Cover.trans ((directedCover Y).pullback₁ f) i ≫
        (pullbackRestrictIsoRestrict f V.1).hom) ≫ (f ⁻¹ᵁ V.1).ι = pullback.fst f U.1.ι :=
      (Category.assoc _ _ _).trans
        ((congrArg (Cover.trans ((directedCover Y).pullback₁ f) i ≫ ·)
          (pullbackRestrictIsoRestrict_hom_ι f V.1)).trans
          ((pullback.lift_fst _ _ _).trans (Category.comp_id _)))
    exact (Category.assoc _ _ _).trans
      ((congrArg ((pullbackRestrictIsoRestrict f U.1).inv ≫ ·) h2).trans
        ((pullbackRestrictIsoRestrict_inv_fst f U.1).trans (Scheme.homOfLE_ι _ _).symm))
  refine (Iso.inv_comp_eq _).mp ?_
  have h1 : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom ≫
        (f ⁻¹ᵁ V.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F V.1).subtype) ≫ (relCover H).f V =
      X.homOfLE (f.preimage_mono (toOpens_mono i.1.1)) ≫
        (f ⁻¹ᵁ V.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F V.1).subtype) ≫ (relCover H).f V :=
    (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (f ⁻¹ᵁ V.1).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (F V.1).subtype) ≫ (relCover H).f V) this))
  refine h1.trans ?_
  have hres : X.homOfLE (f.preimage_mono (toOpens_mono i.1.1)) ≫
      (f ⁻¹ᵁ V.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F V.1).subtype) ≫ (relCover H).f V =
      (f ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (X.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.1.1))).op) ≫
        Spec.map (CommRingCat.ofHom (F V.1).subtype) ≫ (relCover H).f V :=
    (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc ..).symm
  refine hres.trans (congrArg ((f ⁻¹ᵁ U.1).toSpecΓ ≫ ·) ?_)
  have hring : CommRingCat.ofHom (F V.1).subtype ≫
      X.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.1.1))).op =
      (diagram H).map i.op ≫ CommRingCat.ofHom (F U.1).subtype := by
    ext x; rfl
  have hsp : Spec.map (X.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.1.1))).op) ≫
      Spec.map (CommRingCat.ofHom (F V.1).subtype) ≫ (relCover H).f V =
      Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫
        Spec.map ((diagram H).map i.op) ≫ (relCover H).f V :=
    (Spec.map_comp_assoc (CommRingCat.ofHom (F V.1).subtype)
      (X.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.1.1))).op) _).symm.trans
      ((congrArg (fun φ => Spec.map φ ≫ (relCover H).f V) hring).trans
        (Spec.map_comp_assoc ((diagram H).map i.op) (CommRingCat.ofHom (F U.1).subtype) _))
  exact hsp.trans (congrArg (Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ ·)
    (colimit.w (glueData H).functor i))

@[reassoc]
lemma ι_toRel (H : QCohSub f F) (U : Y.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toRel H = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ (relCover H).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ toRel H
  · congr 1; simp; rfl
  delta toRel
  generalize_proofs _ _ _ _ H'
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H' _

def fromRel (H : QCohSub f F) : relSpec H ⟶ Y := (glueData H).toBase

lemma ι_fromRel (H : QCohSub f F) (U : Y.affineOpens) :
    (relCover H).f U ≫ fromRel H =
      Spec.map ((diagramMap H).app (.op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma fromRel_preimage (H : QCohSub f F) (U : Y.affineOpens) :
    fromRel H ⁻¹ᵁ U = ((relCover H).f U).opensRange := by
  simpa using! (glueData H).toBase_preimage_eq_opensRange_ι U

lemma toRel_fromRel (H : QCohSub f F) : toRel H ≫ fromRel H = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  let V : Y.affineOpens := U
  have hV : IsAffineOpen V.1 := V.2
  change (f ⁻¹ᵁ V.1).ι ≫ toRel H ≫ fromRel H = (f ⁻¹ᵁ V.1).ι ≫ f
  refine (ι_toRel_assoc H V _).trans ?_
  have hring : (diagramMap H).app (.op V) ≫ CommRingCat.ofHom (F V.1).subtype = f.app V.1 := by
    ext x; rfl
  have h2 : (Spec.map (CommRingCat.ofHom (F V.1).subtype) ≫ (relCover H).f V) ≫ fromRel H =
      Spec.map (f.app V.1) ≫ hV.fromSpec :=
    (Category.assoc _ _ _).trans
      ((congrArg (Spec.map _ ≫ ·) (ι_fromRel H V)).trans
        ((Spec.map_comp_assoc _ _ _).symm.trans
          (congrArg (fun φ => Spec.map φ ≫ hV.fromSpec) hring)))
  refine (congrArg ((f ⁻¹ᵁ V.1).toSpecΓ ≫ ·) h2).trans ?_
  simp [hV.toSpecΓ_fromSpec]

private def isFiniteProp : MorphismProperty Scheme.{0} := fun _ _ h => IsFinite h

private lemma isZariskiLocalAtTarget_isFiniteProp : IsZariskiLocalAtTarget isFiniteProp :=
  (HasAffineProperty.iff.mp
    ((HasAffineProperty.affineAnd_iff isFiniteProp RingHom.finite_respectsIso
      RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan).mpr
      isFinite_iff)).1

lemma isFinite_fromRel (H : QCohSub f F)
    (hfin : ∀ U : Y.affineOpens, ((diagramMap H).app (.op U)).hom.Finite) : IsFinite (fromRel H) := by
  have := isZariskiLocalAtTarget_isFiniteProp
  change isFiniteProp (fromRel H)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := isFiniteProp) _
    (iSup_affineOpens_eq_top _)]
  intro U
  have hU : IsAffineOpen U.1 := U.2
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let e := IsOpenImmersion.isoOfRangeEq (fromRel H ⁻¹ᵁ U.1).ι ((relCover H).f U)
      (by simpa using congr($(fromRel_preimage H U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso isFiniteProp e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso isFiniteProp _ hU.isoSpec.hom]
  change IsFinite _
  convert! (IsFinite.SpecMap_iff _).mpr (hfin U)
  refine (cancel_mono hU.fromSpec).mp ?_
  simp [IsAffineOpen.isoSpec_hom, hU.toSpecΓ_fromSpec, e, ι_fromRel]
  rfl

def relObjIso (H : QCohSub f F) {U : Y.Opens} (hU : IsAffineOpen U) :
    Γ(relSpec H, fromRel H ⁻¹ᵁ U) ≅ .of (F U) :=
  have : IsOpenImmersion ((relCover H).f ⟨U, hU⟩) := (relCover H).map_prop ⟨U, hU⟩
  (relSpec H).presheaf.mapIso (eqToIso
    ((Scheme.Hom.image_top_eq_opensRange _).trans (fromRel_preimage H ⟨U, hU⟩).symm)).op ≪≫
  ((relCover H).f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

lemma toRel_app_preimage (H : QCohSub f F) (U : Y.affineOpens) :
    (toRel H).app (fromRel H ⁻¹ᵁ ↑U) =
      (relObjIso H U.2).hom ≫
      CommRingCat.ofHom (F U.1).subtype ≫
      X.presheaf.map (eqToHom (by
        rw [← Scheme.Hom.comp_preimage (toRel H) (fromRel H), toRel_fromRel])).op := by
  let V : (relSpec H).Opens := fromRel H ⁻¹ᵁ U.1
  let W : X.Opens := f ⁻¹ᵁ U.1
  let c : Spec (.of (F U.1)) ⟶ relSpec H := (relCover H).f U
  have : IsOpenImmersion c := (relCover H).map_prop U
  have hpre : toRel H ⁻¹ᵁ V = W := by
    dsimp only [V, W]
    rw [← Scheme.Hom.comp_preimage, toRel_fromRel]
  have hopen : c ''ᵁ ⊤ = V :=
    (Scheme.Hom.image_top_eq_opensRange c).trans (fromRel_preimage H U).symm
  have hι : W.ι ≫ toRel H = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ c :=
    ι_toRel H U
  have hle_lhs : ⊤ ≤ (W.ι ≫ toRel H) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, hpre, Scheme.Opens.ι_preimage_self]
  have hle_rhs : ⊤ ≤ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ c) ⁻¹ᵁ V :=
    hι ▸ hle_lhs
  have hcongr_aux : ∀ {g₁ g₂ : W.toScheme ⟶ relSpec H} (e : g₁ = g₂)
      (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ V) (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ V),
      g₁.appLE V ⊤ h₁ = g₂.appLE V ⊤ h₂ := by
    rintro g₁ _ rfl _ _; rfl
  have hlhs : (W.ι ≫ toRel H).appLE V ⊤ hle_lhs =
      (toRel H).appLE V W hpre.ge ≫ W.topIso.inv := by
    rw [← Scheme.Hom.appLE_comp_appLE W.ι (toRel H) V W ⊤ hpre.ge W.ι_preimage_self.ge]
    congr 1
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hc_le : ⊤ ≤ c ⁻¹ᵁ V := by
    rw [← hopen]
    exact (Scheme.Hom.preimage_image_eq c ⊤).ge
  have hc_app : c.appLE V ⊤ hc_le =
      (relSpec H).presheaf.map (eqToHom hopen).op ≫ (c.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  have hsc_le : ⊤ ≤ (Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ c) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, ← hopen, Scheme.Hom.preimage_image_eq, Scheme.Hom.preimage_top]
  have hrhs : (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ c).appLE V ⊤ hle_rhs =
      (relSpec H).presheaf.map (eqToHom hopen).op ≫ (c.appIso ⊤).hom ≫
        (Scheme.ΓSpecIso (.of (F U.1))).hom ≫ CommRingCat.ofHom (F U.1).subtype ≫ W.topIso.inv := by
    have appLE_top : ∀ {A B : Scheme} (g : A ⟶ B), g.appLE ⊤ ⊤ le_top = g.appTop :=
      fun {A _} g =>
        (congrArg (g.app ⊤ ≫ ·) (A.presheaf.map_id (Opposite.op (g ⁻¹ᵁ ⊤)))).trans
          (Category.comp_id (g.app ⊤))
    have h1 : (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ c).appLE V ⊤ hle_rhs =
        c.appLE V ⊤ hc_le ≫
          (Spec.map (CommRingCat.ofHom (F U.1).subtype)).appTop ≫ W.toSpecΓ.appTop := by
      have ha := Scheme.Hom.appLE_comp_appLE W.toSpecΓ
        (Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ c) V ⊤ ⊤ hsc_le le_top
      have hb := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (F U.1).subtype)) c
        V ⊤ ⊤ hc_le le_top
      rw [← ha, ← hb, appLE_top, appLE_top, Category.assoc]
    have hnat : (Spec.map (CommRingCat.ofHom (F U.1).subtype)).appTop ≫
        (Scheme.ΓSpecIso Γ(X, W)).hom ≫ W.topIso.inv =
        (Scheme.ΓSpecIso (.of (F U.1))).hom ≫ CommRingCat.ofHom (F U.1).subtype ≫ W.topIso.inv :=
      Scheme.ΓSpecIso_naturality_assoc (CommRingCat.ofHom (F U.1).subtype) W.topIso.inv
    rw [h1, hc_app, Scheme.Opens.toSpecΓ_appTop, hnat, Category.assoc]
  have happLE : (toRel H).appLE V W hpre.ge =
      (relObjIso H U.2).hom ≫ CommRingCat.ofHom (F U.1).subtype := by
    refine (cancel_mono W.topIso.inv).mp ?_
    calc
      (toRel H).appLE V W hpre.ge ≫ W.topIso.inv = (W.ι ≫ toRel H).appLE V ⊤ hle_lhs := hlhs.symm
      _ = (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ c).appLE V ⊤ hle_rhs :=
            hcongr_aux hι hle_lhs hle_rhs
      _ = (relSpec H).presheaf.map (eqToHom hopen).op ≫ (c.appIso ⊤).hom ≫
            (Scheme.ΓSpecIso (.of (F U.1))).hom ≫ CommRingCat.ofHom (F U.1).subtype ≫ W.topIso.inv := hrhs
      _ = ((relObjIso H U.2).hom ≫ CommRingCat.ofHom (F U.1).subtype) ≫ W.topIso.inv := by
            simp only [relObjIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
            rfl
  calc
    (toRel H).app V = (toRel H).appLE V W hpre.ge ≫ X.presheaf.map (eqToHom hpre).op := by
      rw [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
      change (toRel H).app V = (toRel H).app V ≫ X.presheaf.map (𝟙 _)
      rw [X.presheaf.map_id, Category.comp_id]
    _ = (relObjIso H U.2).hom ≫ CommRingCat.ofHom (F U.1).subtype ≫
          X.presheaf.map (eqToHom hpre).op := by
      rw [happLE, Category.assoc]

lemma relObjIso_hom_subtype (H : QCohSub f F) {U : Y.Opens} (hU : IsAffineOpen U) :
    (relObjIso H hU).hom ≫ CommRingCat.ofHom (F U).subtype =
    (toRel H).appLE _ _ (by
      rw [← Scheme.Hom.comp_preimage (toRel H) (fromRel H), toRel_fromRel]) := by
  rw [Hom.appLE, toRel_app_preimage H ⟨U, hU⟩, Category.assoc]
  simp [← Functor.map_comp]
  rfl

lemma isDominant_toRel (H : QCohSub f F) (hfin : IsFinite (fromRel H)) : IsDominant (toRel H) := by
  have hqc : QuasiCompact (toRel H) := by
    apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ (fromRel H)
    · infer_instance
    · rw [toRel_fromRel]
      infer_instance
  have hker : (toRel H).ker = ⊥ := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun U : Y.affineOpens ↦ ⟨fromRel H ⁻¹ᵁ U.1, U.2.preimage _⟩)
      (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U ↦ ?_
    simp only [Hom.ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot,
      ← ConcreteCategory.mono_iff_injective_of_preservesPullback, ← MorphismProperty.monomorphisms]
    simp only [toRel_app_preimage,
      eqToHom_op, MorphismProperty.cancel_left_of_respectsIso,
      MorphismProperty.cancel_right_of_respectsIso]
    rw [MorphismProperty.monomorphisms, @ConcreteCategory.mono_iff_injective_of_preservesPullback]
    exact Subtype.val_injective
  have := congr(($(hker).support : Set (relSpec H)))
  rw [IdealSheafData.support_bot, Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

lemma isReduced_relSpec (H : QCohSub f F) [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced (relSpec H) :=
  have (i : _) : AlgebraicGeometry.IsReduced ((relCover H).X i) := by
    have : _root_.IsReduced ((diagram H).obj (.op i)) :=
      isReduced_of_injective (F i.1).subtype Subtype.val_injective
    change AlgebraicGeometry.IsReduced (Spec ((diagram H).obj (.op i)))
    infer_instance
  .of_openCover _ (relCover H)

lemma isIntegral_relSpec (H : QCohSub f F) [AlgebraicGeometry.IsIntegral X] [IsDominant (toRel H)] :
    AlgebraicGeometry.IsIntegral (relSpec H) :=
  have := isReduced_relSpec H
  have : IrreducibleSpace (relSpec H) := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          (toRel H).continuous.continuousOn).closure
    simpa using (toRel H).denseRange.closure_range.symm
  isIntegral_of_irreducibleSpace_of_isReduced _

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_finite_cover {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [AlgebraicGeometry.IsIntegral S]
    [IsDominant gp] (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)) (hF : GlobalTheory.Mum.IsFinSub gp F) :
    ∃ (S' : Scheme) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ AlgebraicGeometry.IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (GlobalTheory.Mum.le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  have H : QCohSub gp F := ⟨h1, h2, h3⟩
  have : AlgebraicGeometry.IsIntegral (Sp K) := inferInstanceAs (AlgebraicGeometry.IsIntegral (Spec (.of K)))
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : TopologicalSpace.NoetherianSpace (Sp K) := inferInstance
  have : QuasiCompact gp := inferInstance
  have : QuasiSeparated gp := inferInstance
  have hfin : IsFinite (fromRel H) := by
    refine isFinite_fromRel H fun U ↦ ?_
    obtain ⟨t, ht, hx⟩ := h4 U.1 U.2
    let : Algebra Γ(S, U.1) (F U.1) :=
      ((gp.app U.1).hom.codRestrict (F U.1) (h1 _ U.2)).toAlgebra
    change Module.Finite Γ(S, U.1) (F U.1)
    refine Module.Finite.of_fg_top ?_
    rw [Submodule.fg_def]
    refine ⟨Set.range (fun y : t ↦ (⟨y.1, ht y.1 y.2⟩ : F U.1)), Set.finite_range _, ?_⟩
    rw [eq_top_iff]
    rintro x -
    obtain ⟨c, hc⟩ := hx x.1 x.2
    have : x = ∑ y : t, c y.1 • (⟨y.1, ht y.1 y.2⟩ : F U.1) := by
      apply Subtype.ext
      rw [hc, AddSubmonoidClass.coe_finsetSum, ← Finset.sum_coe_sort]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun y _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  have := isDominant_toRel H hfin
  refine ⟨relSpec H, fromRel H, toRel H, toRel_fromRel H, hfin, isIntegral_relSpec H, this, ?_⟩
  intro V hV x hx
  refine ⟨(relObjIso H hV).inv.hom ⟨x, hx⟩, ?_⟩
  rw [← relObjIso_hom_subtype H hV, ← CommRingCat.comp_apply, Iso.inv_hom_id_assoc]
  rfl

end GlobalTheory.RelativeSpectrum
