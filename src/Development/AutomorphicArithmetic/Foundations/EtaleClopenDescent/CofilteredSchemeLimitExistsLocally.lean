module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0055

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Cb.GluingProjections

variable {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (j₀ : J)

private def res {V U : (D.obj j₀).Opens} (h : V ≤ U) : opensDiagram D j₀ V ⟶ opensDiagram D j₀ U where
  app j := Scheme.homOfLE _ (Scheme.Hom.preimage_mono _ h)
  naturality j k f := by
    dsimp only [opensDiagram]
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp

private def q (U : (D.obj j₀).Opens) : opensDiagram D j₀ U ⟶ (Functor.const _).obj (U : Scheme) where
  app j := D.map j.hom ∣_ U
  naturality j k f := by
    dsimp only [opensDiagram]
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp [morphismRestrict_ι, ← D.map_comp]

private lemma isPullback_res {V U : (D.obj j₀).Opens} (h : V ≤ U) (j : Over j₀) :
    IsPullback ((res D j₀ h).app j) ((q D j₀ V).app j) ((q D j₀ U).app j) ((D.obj j₀).homOfLE h) := by
  have t := (isPullback_morphismRestrict (D.map j.hom) U).flip
  have s := (isPullback_morphismRestrict (D.map j.hom) V).flip
  dsimp only [res, q, opensDiagram]
  refine IsPullback.of_right (h₁₂ := (D.map j.hom ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ ?_ t
  · convert s using 1
    all_goals first
      | rfl
      | exact Scheme.homOfLE_ι _ _
  · rw [← cancel_mono U.ι]
    simp [Category.assoc, morphismRestrict_ι]

private abbrev T : Over j₀ := Over.mk (𝟙 j₀)

private lemma cone_q {U : (D.obj j₀).Opens} (c : Cone (opensDiagram D j₀ U)) (j : Over j₀) :
    c.π.app j ≫ (q D j₀ U).app j = c.π.app (T j₀) ≫ (q D j₀ U).app (T j₀) := by
  have f : j ⟶ T j₀ := Over.homMk j.hom
  have h1 := c.w f
  have h2 := (q D j₀ U).naturality f
  rw [← h1, Category.assoc, h2]
  simp

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

private lemma isPullback_limMap {V U : (D.obj j₀).Opens} (h : V ≤ U) [HasLimit (opensDiagram D j₀ V)]
    [HasLimit (opensDiagram D j₀ U)] :
    IsPullback (limMap (res D j₀ h)) (limit.π _ (T j₀) ≫ (q D j₀ V).app (T j₀))
      (limit.π _ (T j₀) ≫ (q D j₀ U).app (T j₀)) ((D.obj j₀).homOfLE h) := by
  have hU : ∀ j, limit.π (opensDiagram D j₀ U) j ≫ (q D j₀ U).app j =
      limit.π (opensDiagram D j₀ U) (T j₀) ≫ (q D j₀ U).app (T j₀) :=
    fun j => cone_q D j₀ (limit.cone _) j
  have hV : ∀ j, limit.π (opensDiagram D j₀ V) j ≫ (q D j₀ V).app j =
      limit.π (opensDiagram D j₀ V) (T j₀) ≫ (q D j₀ V).app (T j₀) :=
    fun j => cone_q D j₀ (limit.cone _) j
  have w : limMap (res D j₀ h) ≫ limit.π _ (T j₀) ≫ (q D j₀ U).app (T j₀) =
      (limit.π _ (T j₀) ≫ (q D j₀ V).app (T j₀)) ≫ (D.obj j₀).homOfLE h := by
    rw [limMap_π_assoc, Category.assoc, (isPullback_res D j₀ h (T j₀)).w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w (fun s => limit.lift _
    { pt := s.pt
      π :=
        { app := fun j => (isPullback_res D j₀ h j).lift (s.fst ≫ limit.π _ j) s.snd
            (by rw [Category.assoc, hU j]; exact s.condition)
          naturality := fun j k f => by
            apply (isPullback_res D j₀ h k).hom_ext
            · simp only [Functor.const_obj_map, Category.assoc,
                IsPullback.lift_fst, (res D j₀ h).naturality f, IsPullback.lift_fst_assoc,
                limit.w]
              simp
            · simp only [Functor.const_obj_map, Category.assoc,
                IsPullback.lift_snd, (q D j₀ V).naturality f]
              simp } }) ?_ ?_ ?_⟩⟩
  · intro s
    refine limit.hom_ext fun j => ?_
    simp
  · intro s
    simp
  · intro s m h1 h2
    refine limit.hom_ext fun j => ?_
    apply (isPullback_res D j₀ h j).hom_ext
    · simp only [limit.lift_π, IsPullback.lift_fst, Category.assoc]
      rw [← h1]
      simp
    · simp only [limit.lift_π, IsPullback.lift_snd, Category.assoc]
      rw [hV j, ← Category.assoc]
      exact h2

private abbrev coverOpen (U : (D.obj j₀).directedAffineCover.I₀) : (D.obj j₀).Opens := U.1

private lemma coverOpen_le {U V : (D.obj j₀).directedAffineCover.I₀} (f : U ⟶ V) :
    coverOpen D j₀ U ≤ coverOpen D j₀ V := leOfHom f

section Glue

variable [∀ U : (D.obj j₀).directedAffineCover.I₀, HasLimit (opensDiagram D j₀ U.1)]

private def P : (D.obj j₀).directedAffineCover.I₀ ⥤ Scheme.{0} where
  obj U := limit (opensDiagram D j₀ (coverOpen D j₀ U))
  map {U V} f := limMap (res D j₀ (coverOpen_le D j₀ f))
  map_id U := by
    refine limit.hom_ext fun j => ?_
    rw [limMap_π, Category.id_comp]
    dsimp only [res, opensDiagram]
    simp
  map_comp f g := by
    refine limit.hom_ext fun j => ?_
    rw [limMap_π, Category.assoc, limMap_π, limMap_π_assoc]
    dsimp only [res, opensDiagram]
    simp

private def pr : P D j₀ ⟶ (D.obj j₀).directedAffineCover.functorOfLocallyDirected where
  app U := limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) (T j₀) ≫ (q D j₀ (coverOpen D j₀ U)).app (T j₀)
  naturality {_U _V} f := (isPullback_limMap D j₀ (coverOpen_le D j₀ f)).w

private def gd : (D.obj j₀).directedAffineCover.RelativeGluingData where
  functor := P D j₀
  natTrans := pr D j₀
  equifibered {_U _V} f := isPullback_limMap D j₀ (coverOpen_le D j₀ f)

private def glπ (j : Over j₀) : (gd D j₀).glued ⟶ D.obj j.left :=
  colimit.desc (gd D j₀).functor
    { pt := D.obj j.left
      ι :=
        { app U := limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) j ≫
            (opensDiagramι D j₀ (coverOpen D j₀ U)).app j
          naturality {U V} f := by
            have h1 : (res D j₀ (coverOpen_le D j₀ f)).app j ≫
                (opensDiagramι D j₀ (coverOpen D j₀ V)).app j =
                (opensDiagramι D j₀ (coverOpen D j₀ U)).app j :=
              Scheme.homOfLE_ι (D.obj j.left) (Scheme.Hom.preimage_mono _ (coverOpen_le D j₀ f))
            exact (limMap_π_assoc (res D j₀ (coverOpen_le D j₀ f)) j
              ((opensDiagramι D j₀ (coverOpen D j₀ V)).app j)).trans
              ((congrArg (limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) j ≫ ·) h1).trans
                (Category.comp_id _).symm) } }

private lemma ι_glπ (U : (D.obj j₀).directedAffineCover.I₀) (j : Over j₀) :
    colimit.ι (gd D j₀).functor U ≫ glπ D j₀ j =
      limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) j ≫
        (opensDiagramι D j₀ (coverOpen D j₀ U)).app j := by
  dsimp only [glπ]
  exact colimit.ι_desc _ U

private lemma gluing_projection_T_eq_base : glπ D j₀ (T j₀) = (gd D j₀).toBase := by
  refine colimit.hom_ext fun U => ?_
  rw [ι_glπ]
  refine Eq.trans ?_ ((gd D j₀).ι_toBase U).symm
  have h : (D.map (𝟙 j₀) ∣_ coverOpen D j₀ U) ≫ (coverOpen D j₀ U).ι =
      (D.map (𝟙 j₀) ⁻¹ᵁ coverOpen D j₀ U).ι := by
    rw [morphismRestrict_ι, D.map_id, Category.comp_id]
  exact (congrArg (limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) (T j₀) ≫ ·) h.symm).trans
    (Category.assoc _ _ _).symm

private def glCone : Cone (Over.forget j₀ ⋙ D) where
  pt := (gd D j₀).glued
  π :=
    { app j := glπ D j₀ j
      naturality j k f := by
        refine colimit.hom_ext fun U => ?_
        change colimit.ι (gd D j₀).functor U ≫ 𝟙 _ ≫ glπ D j₀ k =
          colimit.ι (gd D j₀).functor U ≫ glπ D j₀ j ≫ D.map f.left
        rw [Category.id_comp, ι_glπ, reassoc_of% (ι_glπ D j₀ U j)]
        have := (opensDiagramι D j₀ (coverOpen D j₀ U)).naturality f
        rw [← limit.w (opensDiagram D j₀ (coverOpen D j₀ U)) f, Category.assoc]
        exact congrArg (limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) j ≫ ·) this }

private lemma gl_local_ext {Z : Scheme.{0}} (U : (D.obj j₀).directedAffineCover.I₀)
    (a b : Z ⟶ (gd D j₀).glued) (c : Z ⟶ (D.obj j₀).directedAffineCover.X U)
    (ha : c ≫ (D.obj j₀).directedAffineCover.f U = a ≫ (gd D j₀).toBase)
    (hb : c ≫ (D.obj j₀).directedAffineCover.f U = b ≫ (gd D j₀).toBase)
    (h : ∀ j, a ≫ glπ D j₀ j = b ≫ glπ D j₀ j) : a = b := by
  have hp := (gd D j₀).isPullback_natTrans_ι_toBase U
  generalize ha' : hp.lift c a ha = la
  generalize hb' : hp.lift c b hb = lb
  have ea : a = la ≫ colimit.ι _ U := ha' ▸ (hp.lift_snd _ _ _).symm
  have eb : b = lb ≫ colimit.ι _ U := hb' ▸ (hp.lift_snd _ _ _).symm
  have e : (la : Z ⟶ limit (opensDiagram D j₀ (coverOpen D j₀ U))) = lb := by
    refine limit.hom_ext fun j => ?_
    rw [← cancel_mono ((opensDiagramι D j₀ (coverOpen D j₀ U)).app j)]
    have ha1 : (la ≫ limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) j) ≫
        (opensDiagramι D j₀ (coverOpen D j₀ U)).app j = a ≫ glπ D j₀ j :=
      (Category.assoc _ _ _).trans ((congrArg (la ≫ ·) (ι_glπ D j₀ U j).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ glπ D j₀ j) ea.symm)))
    have hb1 : (lb ≫ limit.π (opensDiagram D j₀ (coverOpen D j₀ U)) j) ≫
        (opensDiagramι D j₀ (coverOpen D j₀ U)).app j = b ≫ glπ D j₀ j :=
      (Category.assoc _ _ _).trans ((congrArg (lb ≫ ·) (ι_glπ D j₀ U j).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ glπ D j₀ j) eb.symm)))
    exact ha1.trans ((h j).trans hb1.symm)
  rw [ea, eb, e]

private lemma gl_hom_ext {Y : Scheme.{0}} (a b : Y ⟶ (gd D j₀).glued)
    (h : ∀ j, a ≫ glπ D j₀ j = b ≫ glπ D j₀ j) : a = b := by
  have hab : a ≫ (gd D j₀).toBase = b ≫ (gd D j₀).toBase := by
    rw [← gluing_projection_T_eq_base]
    exact h (T j₀)
  refine Scheme.Cover.hom_ext
    ((D.obj j₀).directedAffineCover.pullback₁ (a ≫ (gd D j₀).toBase)) _ _ fun U => ?_
  change pullback.fst _ _ ≫ a = pullback.fst _ _ ≫ b
  refine gl_local_ext D j₀ U _ _ (pullback.snd _ _) ?_ ?_ ?_
  · rw [Category.assoc]
    exact pullback.condition.symm
  · rw [Category.assoc, ← hab]
    exact pullback.condition.symm
  · intro j
    simp only [Category.assoc]
    rw [h j]

section Lift

variable (s : Cone (Over.forget j₀ ⋙ D))

private abbrev sT : s.pt ⟶ D.obj j₀ := s.π.app (T j₀)

omit [∀ U : (D.obj j₀).directedAffineCover.I₀, HasLimit (opensDiagram D j₀ U.1)] in
private lemma s_w (j : Over j₀) : s.π.app j ≫ D.map j.hom = sT D j₀ s :=
  s.w (Over.homMk j.hom : j ⟶ T j₀)

private def leg (U : (D.obj j₀).Opens) (j : Over j₀) :
    pullback (sT D j₀ s) U.ι ⟶ (opensDiagram D j₀ U).obj j :=
  (isPullback_morphismRestrict (D.map j.hom) U).lift (pullback.snd _ _)
    (pullback.fst _ _ ≫ s.π.app j)
    (pullback.condition.symm.trans
      ((Category.assoc _ _ _).trans (congrArg (pullback.fst _ _ ≫ ·) (s_w D j₀ s j))).symm)

omit [∀ U : (D.obj j₀).directedAffineCover.I₀, HasLimit (opensDiagram D j₀ U.1)] in
private lemma leg_ι (U : (D.obj j₀).Opens) (j : Over j₀) :
    leg D j₀ s U j ≫ (opensDiagramι D j₀ U).app j = pullback.fst _ _ ≫ s.π.app j := by
  dsimp only [leg, opensDiagramι]
  exact (isPullback_morphismRestrict (D.map j.hom) U).lift_snd _ _ _

private def legCone (U : (D.obj j₀).Opens) : Cone (opensDiagram D j₀ U) where
  pt := pullback (sT D j₀ s) U.ι
  π :=
    { app j := leg D j₀ s U j
      naturality j k f := by
        rw [← cancel_mono ((opensDiagramι D j₀ U).app k)]
        have h1 := (opensDiagramι D j₀ U).naturality f
        have h2 := s.w f
        simp only [Functor.const_obj_map, Category.assoc, h1, leg_ι]
        rw [reassoc_of% (leg_ι D j₀ s U j), h2]
        exact Category.id_comp _ }

private def pullOpen (U : ((D.obj j₀).directedAffineCover.pullback₁ (sT D j₀ s)).I₀) :
    (D.obj j₀).directedAffineCover.I₀ := U

private def locLift (U : ((D.obj j₀).directedAffineCover.pullback₁ (sT D j₀ s)).I₀) :
    ((D.obj j₀).directedAffineCover.pullback₁ (sT D j₀ s)).X U ⟶ (gd D j₀).glued :=
  limit.lift _ (legCone D j₀ s (coverOpen D j₀ (pullOpen D j₀ s U))) ≫
    colimit.ι (gd D j₀).functor (pullOpen D j₀ s U)

private lemma locLift_glπ (U : ((D.obj j₀).directedAffineCover.pullback₁ (sT D j₀ s)).I₀) (j : Over j₀) :
    locLift D j₀ s U ≫ glπ D j₀ j =
      ((D.obj j₀).directedAffineCover.pullback₁ (sT D j₀ s)).f U ≫ s.π.app j :=
  (Category.assoc _ _ _).trans
    ((congrArg (limit.lift _ _ ≫ ·) (ι_glπ D j₀ (pullOpen D j₀ s U) j)).trans
      ((limit.lift_π_assoc _ _ _).trans (leg_ι D j₀ s (coverOpen D j₀ (pullOpen D j₀ s U)) j)))

private def glLift : s.pt ⟶ (gd D j₀).glued :=
  Scheme.Cover.glueMorphisms ((D.obj j₀).directedAffineCover.pullback₁ (sT D j₀ s))
    (fun U => locLift D j₀ s U) (fun U V => by
      refine gl_hom_ext D j₀ _ _ fun j => ?_
      rw [Category.assoc, Category.assoc, locLift_glπ, locLift_glπ]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ s.π.app j) pullback.condition).trans (Category.assoc _ _ _)))

private lemma glLift_glπ (j : Over j₀) : glLift D j₀ s ≫ glπ D j₀ j = s.π.app j := by
  refine Scheme.Cover.hom_ext ((D.obj j₀).directedAffineCover.pullback₁ (sT D j₀ s)) _ _
    fun U => ?_
  rw [glLift, Scheme.Cover.ι_glueMorphisms_assoc, locLift_glπ]

end Lift

private def isLimitGlCone : IsLimit (glCone D j₀) where
  lift s := glLift D j₀ s
  fac s j := glLift_glπ D j₀ s j
  uniq s m hm := gl_hom_ext D j₀ _ _ fun j => by
    rw [glLift_glπ]
    exact hm j

end Glue

end UpperTheory.Cb.GluingProjections

theorem UpperTheory.Cb.cofiltered_scheme_limit_exists_locally :
    LateralTheory.E.BuildCut.LimInt → LateralTheory.E.t_E2Cut.Cont → LateralTheory.E.t_E2Cut.MV → LateralTheory.E.HasLimPf.Loc := by
  intro _ _ _ J _ _ D j₀ _ hlim
  letI : ∀ U : (D.obj j₀).directedAffineCover.I₀,
      HasLimit (opensDiagram D j₀ U.1) :=
    fun U => hlim U.1 U.2
  exact ⟨⟨⟨UpperTheory.Cb.GluingProjections.glCone D j₀, UpperTheory.Cb.GluingProjections.isLimitGlCone D j₀⟩⟩⟩
