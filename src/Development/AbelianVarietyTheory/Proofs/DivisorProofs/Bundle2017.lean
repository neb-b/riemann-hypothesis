module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismsIntoAffineOpenMilnorSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem glue_into_affineOpen (S : Scheme.{0}) [IsAffine S] (U T T₁ T₂ T₀ : Over S) (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) (hM : Milnor j₁.left j₂.left k₁.left k₂.left) (V : U.left.Opens)
    (hV : IsAffineOpen V) (u₁ : T₁ ⟶ U) (u₂ : T₂ ⟶ U) (hk : k₁ ≫ u₁ = k₂ ≫ u₂)
    (h₁ : ∀ x, u₁.left x ∈ V) (h₂ : ∀ x, u₂.left x ∈ V) :
    ∃ u : T ⟶ U, j₁ ≫ u = u₁ ∧ j₂ ≫ u = u₂ := by
  haveI : IsAffine V.toScheme := hV
  have r₁ : Set.range u₁.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₁ x
  have r₂ : Set.range u₂.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₂ x
  set a₁ := IsOpenImmersion.lift V.ι u₁.left r₁ with ha₁
  set a₂ := IsOpenImmersion.lift V.ι u₂.left r₂ with ha₂
  have f₁ : a₁ ≫ V.ι = u₁.left := IsOpenImmersion.lift_fac _ _ _
  have f₂ : a₂ ≫ V.ι = u₂.left := IsOpenImmersion.lift_fac _ _ _
  have hk' : k₁.left ≫ a₁ = k₂.left ≫ a₂ := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, f₁, f₂]
    exact congrArg CommaMorphism.left hk
  have w : a₁.appTop ≫ k₁.left.appTop = a₂.appTop ≫ k₂.left.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hk']
  set b := hM.cart.lift a₁.appTop a₂.appTop w with hb
  have b₁ : b ≫ j₁.left.appTop = a₁.appTop := hM.cart.lift_fst _ _ _
  have b₂ : b ≫ j₂.left.appTop = a₂.appTop := hM.cart.lift_snd _ _ _
  haveI := hM.aff
  let a : T.left ⟶ V.toScheme := T.left.toSpecΓ ≫ Spec.map b ≫ V.toScheme.isoSpec.inv
  have e₁ : j₁.left ≫ a = a₁ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₁, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have e₂ : j₂.left ≫ a = a₂ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₂, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have hover : (a ≫ V.ι) ≫ U.hom = T.hom := by
    apply ext_of_isAffine
    apply hM.cart.hom_ext
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₁, reassoc_of% f₁, Over.w u₁, Over.w j₁]
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₂, reassoc_of% f₂, Over.w u₂, Over.w j₂]
  refine ⟨Over.homMk (a ≫ V.ι) hover, ?_, ?_⟩
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₁, f₁]
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₂, f₂]

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOpenChartsAdditiveFamiliesRepresenting
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem same_id_map {S : Scheme.{0}} {A T U : Over S} [GrpObj A] {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : Fam A N) (hM : Fam A M) (u : T ⟶ U) :
    Same A N M (𝟙 T) u ↔ (addF A).map u.op (famCls hM) = famCls hN := by
  rw [same_iff_map hN hM, op_id, CategoryTheory.Functor.map_id]
  exact eq_comm

theorem glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  intro S A _ hA Ix U M hM hcov
  obtain ⟨B, x, hu, j, ho, hc, hj⟩ := GlobalTheory.RepOver.representable_over S (addF A) (GlobalTheory.PicGlue.addF_separated S A hA) (GlobalTheory.PicGlue.addF_glue S A hA) Ix U
    (fun i ↦ famCls (hM i).fam)
    (fun i Y u u' h ↦ (hM i).inj Y u u' ((same_iff_map (hM i).fam (hM i).fam u u').2 h))
    (fun i T y ↦ by
      obtain ⟨N, hN, rfl⟩ := famCls_surj y
      obtain ⟨W, hW⟩ := (hM i).chart T N hN
      exact ⟨W, fun Y a ↦ (exists_congr fun u ↦ (same_iff_map hN (hM i).fam a u).symm).trans (hW Y a)⟩)
    (fun T y p ↦ by
      obtain ⟨K, _, _, s, hs⟩ := GlobalTheory.exists_geomPoint_through T.left p
      let a : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
      obtain ⟨N, hN, e⟩ := famCls_surj ((addF A).map a.op y)
      obtain ⟨i, u, h⟩ := hcov K (s ≫ T.hom) N hN
      exact ⟨i, _, a, u, hs, e.symm.trans ((same_id_map hN (hM i).fam u).1 h).symm⟩)
  obtain ⟨P, hP, rfl⟩ := famCls_surj x
  refine ⟨B, P, j, ⟨hP, fun T t N hN ↦ ?_⟩, ho, hc, fun i ↦ (same_id_map (hM i).fam hP _).2 (hj i)⟩
  obtain ⟨g, hg, hg'⟩ := hu T (famCls hN)
  have k : ∀ g : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ g)) ↔ (addF A).map g.op (famCls hP) = famCls hN :=
    fun g ↦ (same_id_iff hN.isLB hP.isLB g).symm.trans (same_id_map hN hP g)
  exact ⟨g, ⟨toUnit_unique _ _, (k g).2 hg⟩, fun g' h ↦ hg' g' ((k g').1 h.2)⟩

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem liftObj_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A' _ i' h' hA' hg' F hF
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  obtain ⟨X, i, h, hX, hFil⟩ := H.exists_lift h' hA' hg' hF
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h'.1 hg'
  obtain ⟨e, he, he₀⟩ := _root_.GlobalTheory.SecLift.exists_section_lift R R₀ π hπ hn X A₀ i h hX (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left
    (Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀))
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    rw [Category.assoc, Category.assoc, h.w, Over.w_assoc, Over.w_assoc]
  have hl₁ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (fst X X).left
      = (fst A₀ A₀).left ≫ i := Limits.pullback.lift_fst _ _ _
  have hl₂ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (snd X X).left
      = (snd A₀ A₀).left ≫ i := Limits.pullback.lift_snd _ _ _
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.ShearLift.exists_lift_shear R R₀ I hI π hπ hk H g g A₀ A₀ A' A' i' i' h' h' hA' hA' hg' hg' X X i i h h hX hX
    e e he he he₀ he₀ _ hl₁ hl₂ (𝟙 A₀) (fun d hd ↦ by rw [push_id]; exact hd)
  have hμ : (fst A₀ A₀ ≫ 𝟙 A₀) * snd A₀ A₀ = μ[A₀] := by
    rw [Category.comp_id, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [hμ] at hm
  obtain ⟨_, hp, hab⟩ := _root_.GlobalTheory.LiftGroupLaw.exists_grpObj_isAbelianScheme R R₀ π hπ hn A₀ hA₀ X i h hX e he he₀ _ hl₁ hl₂ m hm
  have hg : SmoothOfRelativeDimension g X.hom := _root_.GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction R R₀ π hπ hn g X A₀ i h hX hg₀
  exact ⟨X, _, i, hp, hab, hg, (schemeFil_eq_liftFil _ hp (P.1 R X g hab hg).1).symm.trans hFil⟩

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift.Hom

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  let x : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have e : x * x = x := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 x x rfl rfl, _root_.mul_one]; rfl)
  have e' : x = 1 := by simpa using e
  have := congrArg (fun z ↦ z.left) e'
  refine this.trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (T : Over S) :
    (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem liftHom_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have pA := (P.1 R A g hA hg).1
  have pB := (P.1 R B g' hB hg').1
  obtain ⟨l, l₁, l₂⟩ : ∃ l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left, l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i ∧
      l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j :=
    ⟨Limits.pullback.lift ((fst A₀ B₀).left ≫ i) ((snd A₀ B₀).left ≫ j) (by
      rw [Category.assoc, Category.assoc, h.1.w, k.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.ShearLift.exists_lift_shear R R₀ I hI π hπ hk H g g' A₀ B₀ A B i j h k hA hB hg hg' A B i j h.1 k.1
    hA.smooth hB.smooth η[A].left η[B].left (Over.w η[A]) (Over.w η[B])
    ((one_left_comp h _).trans (Category.id_comp _)) ((one_left_comp k _).trans (Category.id_comp _)) l l₁ l₂ f₀
    (by rw [schemeFil_eq_liftFil _ h pA, schemeFil_eq_liftFil _ k pB]; exact hf)
  refine _root_.GlobalTheory.HomLift.existsUnique_isMonHom_lift R R₀ π hπ ⟨2, hk ▸ hI⟩ A₀ B₀ A B i j h k hA hB f₀ (lift (𝟙 A) 1 ≫ φ) ?_
  have e : i ≫ (lift (𝟙 A) (1 : A ⟶ B)).left = (lift (𝟙 A₀) (1 : A₀ ⟶ B₀)).left ≫ l := by
    refine Limits.pullback.hom_ext ?_ ?_
    · change (i ≫ _) ≫ (fst A B).left = (_ ≫ l) ≫ (fst A B).left
      rw [Category.assoc, Category.assoc, l₁, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_fst, lift_fst,
        Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
    · change (i ≫ _) ≫ (snd A B).left = (_ ≫ l) ≫ (snd A B).left
      rw [Category.assoc, Category.assoc, l₂, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_snd, lift_snd,
        one_left_comp k, one_left, ← Category.assoc, h.1.w, Category.assoc]
  rw [Over.comp_left, ← Category.assoc, e, Category.assoc, hφ, ← Category.assoc, ← Over.comp_left, comp_mul,
    lift_fst_assoc, lift_snd, _root_.mul_one, Category.id_comp]

end GlobalTheory.SqLift.Hom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem evO_constO (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R) :
    evO G (constO G r) = r := by
  have hw : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  have h1 := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left ⊤ trivial
  have h2 := congrArg (fun q => q.hom ((G.hom.appLE ⊤ ⊤ (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) h1
  refine h2.trans ?_
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (by simp) ≫
      (η[G]).left.app ⊤ ≫ (Functor.mapIso (Spec (CommRingCat.of R)).presheaf
        (eqToIso (show (η[G]).left ⁻¹ᵁ ⊤ = ⊤ by simp)).op ≪≫ Scheme.ΓSpecIso (CommRingCat.of R)).hom = 𝟙 _ := by
    rw [Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE_assoc]
    simp [hw]
    rw [show Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ (by simp) = 𝟙 _ from
      (Scheme.Hom.appLE_eq_app (𝟙 (Sp R))).trans (Scheme.Hom.id_app ⊤)]
    simp
  exact congrArg (fun q => q.hom r) key

end GlobalTheory.FormalOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CharPMatrix

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

def redHom : ℤ_[p] →+* k := (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod

lemma exists_nat_add (z : ℤ_[p]) : ∃ n : ℕ, ∃ w : ℤ_[p], z = n + p * w := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨PadicInt.zmodRepr z, w, by rw [mul_comm, hw]; ring⟩

variable (B : Type) [Ring B] [Algebra k B]

def tensorPadicEquiv : B ⊗[ℤ] ℤ_[p] ≃ₐ[k] B :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (AlgHom.id k B)
      (((algebraMap k B).comp (redHom p k)).toIntAlgHom)
      (by intro x y; exact Algebra.commute_algebraMap_right _ _))
    Algebra.TensorProduct.includeLeft
    (by ext b; simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]; erw [Algebra.TensorProduct.lift_tmul]; simp)
    (by
      apply Algebra.TensorProduct.ext'
      intro b z
      obtain ⟨n, w, rfl⟩ := exists_nat_add p z
      have hp : (p : B) = 0 := by
        rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero]
      simp [redHom, Algebra.TensorProduct.lift_tmul]
      have h1 : b ⊗ₜ[ℤ] ((p : ℤ_[p]) * w) = 0 := by
        rw [show ((p : ℤ_[p]) * w) = (p : ℤ) • w by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, hp, zero_mul,
          TensorProduct.zero_tmul]
      have h2 : b ⊗ₜ[ℤ] (n : ℤ_[p]) = (b * n) ⊗ₜ[ℤ] 1 := by
        rw [show (n : ℤ_[p]) = (n : ℤ) • (1 : ℤ_[p]) by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, Nat.cast_comm]
      rw [TensorProduct.tmul_add, h1, h2, add_zero])

def matrixBaseChange (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K]
    (n : Type) [Fintype n] [DecidableEq n] : K ⊗[R] Matrix n n R ≃ₐ[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n R K).symm.toRingEquiv) (by
    intro c
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Algebra.algebraMap_eq_smul_one])

end GlobalTheory.CharPMatrix

namespace GlobalTheory.UPel.HT


open GlobalTheory.CharPMatrix in
theorem Datum.charP_tensor_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k]
    [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  intro p _ D k _ _ _
  obtain ⟨e⟩ := D.splitP
  have E0 : k ⊗[𝓞 D.F] (𝓞 D.F ⊗[ℤ] ℤ_[p]) ≃ₐ[k] k :=
    (Algebra.TensorProduct.cancelBaseChange ℤ (𝓞 D.F) k k ℤ_[p]).trans (tensorPadicEquiv p k k)
  have E1 := (Algebra.TensorProduct.assoc ℤ (𝓞 D.F) (𝓞 D.F) D.O (𝓞 D.F) ℤ_[p]).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid (𝓞 D.F) (𝓞 D.F) D.O) (AlgEquiv.refl (R := ℤ) (A₁ := ℤ_[p])))
  have E2 := E1.trans e
  exact ⟨(Algebra.TensorProduct.congr E0.symm (AlgEquiv.refl (R := 𝓞 D.F) (A₁ := D.O))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl
      ((Algebra.TensorProduct.comm (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
        (E2.trans (matrixEquivTensor (Fin D.m) (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]))))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p])
      (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F))).symm.trans
    ((Algebra.TensorProduct.congr E0 AlgEquiv.refl).trans
    (matrixBaseChange (𝓞 D.F) k (Fin D.m))))))⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIsEm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lbIso_of_isEmpty {X : Scheme.{0}} [IsEmpty X] (L M : LB X) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have hU : (LB.div M L).U i ⊓ (LB.div M L).U j = ⊥ := by ext x; exact (IsEmpty.false x).elim
  have : Subsingleton Γ(X, (LB.div M L).U i ⊓ (LB.div M L).U j) := by rw [hU]; infer_instance
  exact Subsingleton.elim _ _

theorem hasRepAF_of_isEmpty : ∀ (S : Scheme.{0}) (A S' : Over S) [GrpObj A] (g : ℕ), IsEmpty S'.left →
    HasRepAF A g S' := by
  intro S A S' _ g hS
  have emp : ∀ {Y : Over S} (_ : Y ⟶ S'), IsEmpty Y.left := fun y => ⟨fun p => hS.false (y.left p)⟩
  refine ⟨S', 𝟙 S', LB.triv _, ⟨⟨LB.isLB_triv _, fun Y a a' t => ?_⟩, fun T t N _ => ?_⟩, ?_, ?_⟩
  · have := emp t; exact lbIso_of_isEmpty _ _
  · have := emp (snd A T ≫ t)
    exact ⟨t, ⟨Category.comp_id _, lbIso_of_isEmpty _ _⟩, fun x hx => (Category.comp_id x).symm.trans hx.1⟩
  · rw [Over.id_left]
    refine ⟨inferInstance, ⟨fun x => isEmptyElim x⟩, ⟨?_⟩⟩
    intro K _ y Z fst snd h
    exact isEmptyElim (y (IsLocalRing.closedPoint K))
  · intro F; exact ⟨⊥, isAffineOpen_bot _, fun x _ => isEmptyElim x⟩

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hasRepAF_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  intro S A _ g Y Y' e h
  obtain ⟨B, b, P, hR, hG, hF⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, ?_⟩, ?_, hF⟩
  · intro T t N hN
    obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨?_, hx2⟩, fun y hy => hu y ⟨?_, hy.2⟩⟩
    · rw [← Category.assoc, hx1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← hy.1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Over.comp_left]
    obtain ⟨hp, hs, hc⟩ := hG
    have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩⟩
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine ⟨inferInstance, ?_, MorphismProperty.RespectsIso.postcomp (@GeometricallyConnected : MorphismProperty Scheme.{0}) e.hom.left b.left hc⟩
    have := smoothOfRelativeDimension_comp (n := g) (m := 0) b.left e.hom.left
    simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.Pair

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem loc_one_add (P : Pair p) (a b a' b' : ℤ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') 1 i j = P.loc a b 1 i j * P.loc a' b' 1 i j := by
  have h₁ : ((P.r i : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h₂ : ((P.r' j : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [loc, one_mul, zpow_add₀ h₁, zpow_add₀ h₂]
  ring

theorem rep_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b a' b' : ℤ) (M M' : HermLB p), P.Rep a b M → P.Rep a' b' M' →
      P.Rep (a + a') (b + b') (M.tens M') := by
  intro k _ X _ p P a b a' b' M M' ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  have e (c : (M.tens M').B.ι) (i : P.L.B.ι) (j : P.A.B.ι) :
      (((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField) / P.loc (a + a') (b + b') 1 i j) =
        ((ρ c.1 : X.functionField) / P.loc a b 1 i j) * ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) := by
    rw [loc_one_add, Units.val_mul]
    ring
  refine ⟨fun c => ρ c.1 * ρ' c.2, GlobalTheory.PtHtComb.isRatSec_tens hρ hρ', ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [e]
    exact (hu x c.1 i j hc.1 hi hj).mul (hu' x c.2 i j hc.2 hi hj)
  · intro σ y c i j hc hi hj
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have u₁ := hu _ c.1 i j (mem_ptsIn.1 hc₁) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have u₂ := hu' _ c.2 i j (mem_ptsIn.1 hc₂) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have n₁ := hn σ y c.1 i j hc₁ hi hj
    have n₂ := hn' σ y c.2 i j hc₂ hi hj
    have z₁ : ‖ratVal ((ρ c.1 : X.functionField) / P.loc a b 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₁)
    have z₂ : ‖ratVal ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₂)
    change Real.log ‖ratVal ((((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField)) /
        P.loc (a + a') (b + b') 1 i j) y‖ - ((M.φ σ).φ c.1 y + (M'.φ σ).φ c.2 y) / 2 = _
    rw [e, ratVal_mul u₁.regAt u₂.regAt, norm_mul, Real.log_mul z₁ z₂]
    push_cast
    linear_combination n₁ + n₂

end GlobalTheory.VolBr.Pair
end
end

