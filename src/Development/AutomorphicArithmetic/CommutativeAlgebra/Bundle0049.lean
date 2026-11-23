module

public import Mathlib
public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0047
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFinrankPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.isPullback_whisker_fst {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) :
    IsPullback (y ▷ G).left (fst T' G).left (fst T G).left y.left := by
  have h : IsPullback (y ▷ G) (fst T' G) (fst T G) y := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.snd (s.fst ≫ snd _ _)) ?_ ?_ ?_⟩⟩
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · simp [s.condition]
      · simp
    · intro s
      simp
    · intro s m h1 h2
      apply CartesianMonoidalCategory.hom_ext
      · simpa using h2
      · simp only [lift_snd]
        rw [← h1, Category.assoc, whiskerRight_snd]
  exact h.map (Over.forget S)

theorem UpperTheory.clopProj_finrank_pullback :
    ∀ {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → ∀ t : T'.left, (UpperTheory.RepresentationRank.proj ((y ▷ G).left ⁻¹ᵁ V)).finrank t = (UpperTheory.RepresentationRank.proj V).finrank (y.left t) := by
  intro S T T' G y V hfin het hcl t
  obtain ⟨hF, hE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hcl
  have hsq := (isPullback_morphismRestrict (y ▷ G).left V).paste_vert (UpperTheory.isPullback_whisker_fst y)
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq t
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfIsSplitOfRank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma tensor_fe {S : Scheme.{0}} (Y₁ Y₂ : Over S) (h1 : IsFinite Y₁.hom) (e1 : Etale Y₁.hom)
    (h2 : IsFinite Y₂.hom) (e2 : Etale Y₂.hom) :
    IsFinite (Y₁ ⊗ Y₂).hom ∧ Etale (Y₁ ⊗ Y₂).hom := by
  have hY : (Y₁ ⊗ Y₂).hom = pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom := rfl
  rw [hY]
  exact ⟨inferInstance, inferInstance⟩

private lemma rep_empty {S : Scheme.{0}} (G : Over S) (hG : IsEmpty G.left) :
    UpperTheory.RepresentationRank.Rep G (Over.mk (𝟙 S)) (⊥ : ((Over.mk (𝟙 S)) ⊗ G).left.Opens) := by
  refine ⟨by simp, fun T V _ => ?_⟩
  have hE : IsEmpty (T ⊗ G).left := ⟨fun x => hG.false ((CartesianMonoidalCategory.snd T G).left x)⟩
  have hV : V = ⊥ := by
    ext x
    exact hE.elim x
  subst hV
  refine ⟨Over.homMk T.hom (by simp), ?_, ?_⟩
  · ext x
    exact hE.elim x
  · intro y _
    ext
    simpa using Over.w y

theorem UpperTheory.exists_clopRep_of_isSplitOfRank :
    ∀ {S : Scheme.{0}} (G : Over S) (n : ℕ), GlobalTheory.FinEt.IsSplitOfRank G.hom n → ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G n
  induction n generalizing G with
  | zero =>
    intro h
    have hG : IsEmpty G.left := (GlobalTheory.FinEt.isSplitOfRank_zero_iff G.hom).1 h
    refine ⟨Over.mk (𝟙 S), ⊥, rep_empty G hG, ?_, ?_⟩
    · show IsFinite (𝟙 S)
      infer_instance
    · show Etale (𝟙 S)
      infer_instance
  | succ n ih =>
    intro h
    obtain ⟨σ, hσ, V, hσp, hrange, hV⟩ := h.exists_of_succ
    obtain ⟨Y₁, U₁, hR₁, hf₁, he₁⟩ := UpperTheory.exists_clopRep_trivial S
    obtain ⟨Y₂, U₂, hR₂, hf₂, he₂⟩ := ih (Over.mk (V.ι ≫ G.hom)) hV
    obtain ⟨U, hU⟩ := UpperTheory.exists_clopRep_of_disjoint_open_cover G (Over.mk (𝟙 S)) (Over.mk (V.ι ≫ G.hom)) Y₁ Y₂
      (Over.homMk σ hσp) (Over.homMk V.ι rfl) U₁ U₂ hσ (show IsOpenImmersion V.ι from inferInstance)
      (show Set.range σ = (Set.range V.ι)ᶜ by rw [hrange, compl_compl]) hR₁ hR₂
    exact ⟨Y₁ ⊗ Y₂, U, hU, tensor_fe Y₁ Y₂ hf₁ he₁ hf₂ he₂⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfRankOfLocallyNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.exists_isPullback_iff_preimage {V₀ X' U₀ X : Scheme.{0}} (v : V₀ ⟶ X') (m : X' ⟶ X) (u : U₀ ⟶ X)
    [IsOpenImmersion v] [IsOpenImmersion u] :
    (∃ w, IsPullback v w m u) ↔ m ⁻¹ᵁ u.opensRange = v.opensRange := by
  constructor
  · rintro ⟨w, hw⟩
    ext x
    change x ∈ m ⁻¹' Set.range u ↔ x ∈ Set.range v
    rw [← Scheme.Pullback.range_fst]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨hw.isoPullback.inv b, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_inv_fst]
    · rintro ⟨a, rfl⟩
      refine ⟨hw.isoPullback.hom a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_hom_fst]
  · intro h
    have hr : Set.range v = Set.range (pullback.fst m u) := by
      rw [Scheme.Pullback.range_fst]
      have := congrArg (fun O : X'.Opens => (O : Set X')) h
      exact this.symm
    let e := IsOpenImmersion.isoOfRangeEq v (pullback.fst m u) hr
    refine ⟨e.hom ≫ pullback.snd m u, IsPullback.of_iso_pullback ⟨?_⟩ e ?_ rfl⟩
    · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr, Category.assoc,
        pullback.condition, Category.assoc]
    · exact IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr

private lemma UpperTheory.pullback_map_symmetry_whisker {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y) :
    pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp) ≫
        (pullbackSymmetry G.hom Y.hom).hom =
      (pullbackSymmetry G.hom T.hom).hom ≫ (y ▷ G).left := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_snd]
    simp
  · erw [pullback.lift_fst]
    simp

private lemma UpperTheory.isPullback_transport_symmetry {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y)
    (V : (T ⊗ G).left.Opens) {U₀ : Scheme.{0}} (u : U₀ ⟶ pullback G.hom Y.hom) (w : (V : Scheme.{0}) ⟶ U₀) :
    IsPullback (V.ι ≫ (pullbackSymmetry G.hom T.hom).inv) w
        (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp)) u ↔
      IsPullback V.ι w (y ▷ G).left (u ≫ (pullbackSymmetry G.hom Y.hom).hom) := by
  have hsq := UpperTheory.pullback_map_symmetry_whisker (G := G) y
  constructor
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom) (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom) ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact hsq
    · simp
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom).symm (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom).symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp

theorem UpperTheory.exists_clopRepOfRank_of_locallyNoetherian :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S), IsFinite G.hom → Etale G.hom → ∀ r : ℕ, ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.RepOfRank r G Y U := by
  intro S _ G hfin het r
  obtain ⟨H, h, U₀, u, hprop, hcl, hfin', hflat', hrk, huniv⟩ :=
    GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper S G.left G.hom hfin inferInstance inferInstance r
  haveI := hprop
  haveI := hcl
  haveI := hfin'
  haveI := hflat'
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : Etale (pullback.snd G.hom h) := inferInstance
  haveI : IsOpenImmersion u :=
    UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale u (pullback.snd G.hom h) inferInstance hcl hflat' inferInstance
  let Y : Over S := Over.mk h
  let ι₀ : U₀ ⟶ (Y ⊗ G).left := u ≫ (pullbackSymmetry G.hom Y.hom).hom
  haveI : IsOpenImmersion ι₀ := by dsimp [ι₀]; infer_instance
  haveI : IsClosedImmersion ι₀ := by dsimp [ι₀]; infer_instance
  refine ⟨Y, ι₀.opensRange, ?_, ?_, ?_⟩
  · exact ι₀.isClosedEmbedding.isClosed_range
  · intro y
    have hp : UpperTheory.RepresentationRank.proj ι₀.opensRange = ι₀.isoOpensRange.inv ≫ (u ≫ pullback.snd G.hom h) := by
      rw [Iso.eq_inv_comp]
      change ι₀.isoOpensRange.hom ≫ (ι₀.opensRange.ι ≫ pullback.fst Y.hom G.hom) = _
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
      simp [ι₀, Y]
    rw [hp, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrk y
  · intro T V hV hVr
    obtain ⟨hVF, hVE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV
    haveI := hVF
    haveI := hVE
    let v : (V : Scheme.{0}) ⟶ pullback G.hom T.hom := V.ι ≫ (pullbackSymmetry G.hom T.hom).inv
    haveI : IsClosedImmersion V.ι :=
      IsClosedImmersion.of_isPreimmersion V.ι (by rw [Scheme.Opens.range_ι]; exact hV)
    haveI : IsClosedImmersion v := by dsimp [v]; infer_instance
    have hvp : v ≫ pullback.snd G.hom T.hom = UpperTheory.RepresentationRank.proj V := by
      simp [v, UpperTheory.RepresentationRank.proj]
    haveI : IsFinite (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; exact hVF
    haveI : Flat (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; infer_instance
    obtain ⟨f, ⟨hf, w, hw⟩, huniq⟩ := huniv T.left T.hom V v inferInstance inferInstance
      inferInstance (fun t => by rw [hvp]; exact hVr t)
    have key : ∀ y' : T ⟶ Y, ((y' ▷ G).left ⁻¹ᵁ ι₀.opensRange = V ↔
        ∃ w, IsPullback v w
          (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y'.left (𝟙 S) (by simp) (by simp)) u) := by
      intro y'
      have h1 := UpperTheory.exists_isPullback_iff_preimage V.ι (y' ▷ G).left ι₀
      rw [Scheme.Opens.opensRange_ι] at h1
      rw [← h1]
      exact exists_congr fun w => (UpperTheory.isPullback_transport_symmetry y' V u w).symm
    refine ⟨Over.homMk f hf, (key _).mpr ⟨w, hw⟩, ?_⟩
    intro y' hy'
    obtain ⟨w', hw'⟩ := (key y').mp hy'
    exact Over.OverMorphism.ext (huniq y'.left ⟨Over.w y', w', hw'⟩)
end

