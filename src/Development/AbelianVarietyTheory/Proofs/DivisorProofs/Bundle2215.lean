module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFlatBaseChangeAffineMilnorSquareOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem isPushout_app_of_isPullback {X X₁ T T₁ : Scheme.{0}} {f : X₁ ⟶ X} {p₁ : X₁ ⟶ T₁} {p : X ⟶ T}
    {j : T₁ ⟶ T} (h : IsPullback f p₁ p j) [IsAffine T] [IsAffine T₁] {W : X.Opens}
    (hW : IsAffineOpen W) :
    IsAffineOpen (f ⁻¹ᵁ W) ∧
      IsPushout (p.appLE ⊤ W le_top) j.appTop (f.app W) (p₁.appLE ⊤ (f ⁻¹ᵁ W) le_top) := by
  have : IsAffine W.toScheme := hW
  have sq : IsPullback (f ∣_ W) ((f ⁻¹ᵁ W).ι ≫ p₁) (W.ι ≫ p) j :=
    (isPullback_morphismRestrict f W).paste_vert h
  have : IsAffine (f ⁻¹ᵁ W).toScheme := IsAffine.of_isPullback sq
  refine ⟨this, ?_⟩
  exact (ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip inferInstance (isAffineOpen_top T) hW le_top le_top).flip

theorem appLE_congr_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (e : a = b) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ a ⁻¹ᵁ U) (h' : V ≤ b ⁻¹ᵁ U) : a.appLE U V h = b.appLE U V h' := by
  subst e; rfl

theorem isPullback_app_of_affine {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W))
    (hV : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V) :
    IsPullback (f₁.app W) (f₂.app W) (g₁.appLE _ V hV₁) (g₂.appLE _ V hV₂) := by
  have := hM.aff; have := hM.aff₁; have := hM.aff₂; have := hM.closed
  obtain ⟨hT₀, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine k₂
  obtain ⟨hU₁, P₁⟩ := isPushout_app_of_isPullback h₁ hW
  obtain ⟨hU₂, P₂⟩ := isPushout_app_of_isPullback h₂ hW
  obtain ⟨-, P₀⟩ := isPushout_app_of_isPullback h₀ hU₂
  have hVe : V = g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := by
    refine le_antisymm hV₂ ?_
    have : g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
    exact this.le.trans hV
  subst hVe
  have e₂ : g₂.appLE (f₂ ⁻¹ᵁ W) (g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) hV₂ = g₂.app (f₂ ⁻¹ᵁ W) :=
    Scheme.Hom.appLE_eq_app ..
  rw [e₂]
  have hfl : (p.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  refine GlobalTheory.T.commRingCat_isPullback_flat_baseChange_surjective _ _ _ _ _ _ _ _ j₁.appTop j₂.appTop k₁.appTop k₂.appTop hM.cart hsurj _ _ _ _ _ _ _ _
    hfl P₁ P₂ P₀ ?_ ?_
  · rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_eq hg _ _ _ _
  · have : k₁.appTop = k₁.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app ..).symm
    rw [this]
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    exact appLE_congr_eq hp _ _ _ _

theorem app_restrict_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U W : Y.Opens} (h : U ≤ W) (a : Γ(Y, W)) :
    f.app U (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem appLE_restrict_eq {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (hU : U' ≤ U) (hV : V' ≤ V) (h : V ≤ g ⁻¹ᵁ U) (h' : V' ≤ g ⁻¹ᵁ U') (a : Γ(Y, U)) :
    g.appLE U' V' h' (Y.presheaf.map (homOfLE hU).op a) =
      X.presheaf.map (homOfLE hV).op (g.appLE U V h a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

theorem elem_of_isPullback_ring {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {i : C ⟶ D} (H : IsPullback f g h i) :
    (∀ x y, f x = f y → g x = g y → x = y) ∧ ∀ b c, h b = i c → ∃ a, f a = b ∧ g a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem sections_of_squares {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] (W : X.Opens) :
    (∀ a b : Γ(X, W), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b) ∧
    ∀ (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)),
      g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)),
        g₁.appLE _ V hV₁ a₁ = g₂.appLE _ V hV₂ a₂ →
          ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂ := by
  have hpre : ∀ U : X.Opens, g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ U) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) := fun U ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
  have aff : ∀ U : X.Opens, IsAffineOpen U → IsPullback (f₁.app U) (f₂.app U)
      (g₁.appLE _ (g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U)) le_rfl) (g₂.appLE _ _ (hpre U).ge) :=
    fun U hU ↦ isPullback_app_of_affine hM h₁ h₂ h₀ hg hp hU _ le_rfl (hpre U).ge le_rfl
  have inj : ∀ (U : X.Opens) (a b : Γ(X, U)), f₁.app U a = f₁.app U b →
      f₂.app U a = f₂.app U b → a = b := by
    intro U a b ha hb
    refine TopCat.Presheaf.section_ext X.sheaf U a b fun x hx ↦ ?_
    change X.presheaf.germ U x hx a = X.presheaf.germ U x hx b
    obtain ⟨U', hU', hxU', hle⟩ := exists_isAffineOpen_mem_and_subset hx
    have hle' : U' ≤ U := hle
    rw [← X.presheaf.germ_res_apply (homOfLE hle') x hxU' a,
      ← X.presheaf.germ_res_apply (homOfLE hle') x hxU' b]
    congr 1
    refine (elem_of_isPullback_ring (aff U' hU')).1 _ _ ?_ ?_
    · rw [app_restrict_eq, app_restrict_eq, ha]
    · rw [app_restrict_eq, app_restrict_eq, hb]
  refine ⟨inj W, ?_⟩
  intro V hV₁ hV₂ hV a₁ a₂ he
  have loc : ∀ x : W, ∃ U : X.Opens, IsAffineOpen U ∧ x.1 ∈ U ∧ ∃ hUW : U ≤ W, ∃ c : Γ(X, U),
      f₁.app U c = X₁.presheaf.map (homOfLE (f₁.preimage_mono hUW)).op a₁ ∧
      f₂.app U c = X₂.presheaf.map (homOfLE (f₂.preimage_mono hUW)).op a₂ := by
    intro x
    obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset x.2
    have hUW : U ≤ W := hle
    refine ⟨U, hU, hxU, hUW, (elem_of_isPullback_ring (aff U hU)).2 _ _ ?_⟩
    have hVU : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) ≤ V := (g₁.preimage_mono (f₁.preimage_mono hUW)).trans hV
    rw [appLE_restrict_eq g₁ (f₁.preimage_mono hUW) hVU hV₁,
      appLE_restrict_eq g₂ (f₂.preimage_mono hUW) hVU hV₂, he]
  choose U hU hxU hUW c hc₁ hc₂ using loc
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 U c := by
    intro x y
    change X.presheaf.map (homOfLE (inf_le_left : U x ⊓ U y ≤ U x)).op (c x) =
      X.presheaf.map (homOfLE (inf_le_right : U x ⊓ U y ≤ U y)).op (c y)
    apply inj
    · rw [app_restrict_eq, app_restrict_eq, hc₁, hc₁, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [app_restrict_eq, app_restrict_eq, hc₂, hc₂, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' U W (fun x ↦ homOfLE (hUW x))
    (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩) c compat
  have ha' : ∀ x, X.presheaf.map (homOfLE (hUW x)).op a = c x := ha
  refine ⟨a, ?_, ?_⟩
  · refine TopCat.Presheaf.section_ext X₁.sheaf _ _ _ fun y hy ↦ ?_
    change X₁.presheaf.germ _ y hy _ = X₁.presheaf.germ _ y hy _
    have hyU : y ∈ f₁ ⁻¹ᵁ U ⟨f₁ y, hy⟩ := hxU ⟨f₁ y, hy⟩
    rw [← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU,
      ← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU a₁,
      ← app_restrict_eq f₁ (hUW ⟨f₁ y, hy⟩) a, ha' ⟨f₁ y, hy⟩, hc₁]
  · refine TopCat.Presheaf.section_ext X₂.sheaf _ _ _ fun y hy ↦ ?_
    change X₂.presheaf.germ _ y hy _ = X₂.presheaf.germ _ y hy _
    have hyU : y ∈ f₂ ⁻¹ᵁ U ⟨f₂ y, hy⟩ := hxU ⟨f₂ y, hy⟩
    rw [← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU,
      ← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU a₂,
      ← app_restrict_eq f₂ (hUW ⟨f₂ y, hy⟩) a, ha' ⟨f₂ y, hy⟩, hc₂]

theorem sections_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → ∀ W : (A ⊗ T).left.Opens, (∀ a b : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = (A ◁ j₁).left.app W b → (A ◁ j₂).left.app W a = (A ◁ j₂).left.app W b → a = b) ∧ ∀ (V : (A ⊗ T₀).left.Opens) (h₁ : V ≤ (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W)) (h₂ : V ≤ (A ◁ k₂).left ⁻¹ᵁ ((A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ((A ⊗ T₁).left, (A ◁ j₁).left ⁻¹ᵁ W)) (a₂ : Γ((A ⊗ T₂).left, (A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left.appLE _ V h₁ a₁ = (A ◁ k₂).left.appLE _ V h₂ a₂ → ∃ a : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = a₁ ∧ (A ◁ j₂).left.app W a = a₂ := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ hM W
  have : Flat (snd A T).left := inferInstanceAs (Flat (pullback.snd A.hom T.hom))
  have hw : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext hM.w
  have hg : (A ◁ k₁).left ≫ (A ◁ j₁).left = (A ◁ k₂).left ≫ (A ◁ j₂).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hw]
  have hp : (A ◁ k₁).left ≫ (snd A T₁).left = (snd A T₀).left ≫ k₁.left := by
    rw [← Over.comp_left, ← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd]
  exact sections_of_squares hM (isPullback_whiskerLeft_snd_left A j₁)
    (isPullback_whiskerLeft_snd_left A j₂) (isPullback_whiskerLeft_snd_left A k₂) hg hp W

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsAtStalkAgreeingOnOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.StalkExt

theorem exists_agree_of_generic {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G]
    [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    (hf : IsMonHom f) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (t : Sp R ⟶ S) [Mono t] (k : Sp (FractionRing R) ⟶ U) (hk : k ≫ j = Out.jK R ≫ t) :
    ∃ g : pullback G.hom t ⟶ H.left, g ≫ H.hom = pullback.fst G.hom t ≫ G.hom ∧
      GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)

  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) k).comp (isGrpPullback_pullback G j)).congr hk rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj H) k).comp (isGrpPullback_pullback H j)).congr hk rfl)
  haveI := ha; haveI := hb; haveI := hf
  have hfK : IsMonHom (a.hom ≫ (Over.pullback k).map f ≫ b.inv) := inferInstance
  have hρ : (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ pullback.fst G.hom j =
      pullback.fst G.hom (Out.jK R ≫ t) := (Category.assoc _ _ _).trans ha'
  have hb2 : b.inv.left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      pullback.fst ((Over.pullback j).obj H).hom k ≫ pullback.fst H.hom j := by
    rw [← hb', ← Category.assoc, ← Over.comp_left, b.inv_hom_id, Over.id_left, Category.id_comp]
  have hK : (a.hom ≫ (Over.pullback k).map f ≫ b.inv).left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ f.left ≫ pullback.fst H.hom j := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb2, ← Category.assoc (((Over.pullback k).map f).left),
      GlobalTheory.ExtUnique.pullback_map_left_fst, Category.assoc, Category.assoc]

  obtain ⟨g, hg, hA⟩ := GlobalTheory.DedekindExt.exists_agree_of_extend (k := Out.jK R) (t := t) rfl G H
    (a.hom ≫ (Over.pullback k).map f ≫ b.inv) fun f' hf' => by
      obtain ⟨F, ⟨-, hF⟩, -⟩ := _root_.GlobalTheory.Desc.semiAbelian_hom_extend_generic R ((Over.pullback t).obj G) ((Over.pullback t).obj H)
        (IsSemiAbelian.pullback t G hG) (IsSemiAbelian.pullback t H hH) f' hf'
      exact ⟨F, hF⟩

  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  let c : pullback G.hom (Out.jK R ≫ t) ⟶ pullback G.hom t :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Out.jK R) (by rw [pullback.condition, Category.assoc])
  have hc₁ : c ≫ pullback.fst G.hom t = pullback.fst G.hom (Out.jK R ≫ t) := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd G.hom t = pullback.snd G.hom (Out.jK R ≫ t) ≫ Out.jK R := pullback.lift_snd _ _ _
  have sq : IsPullback c (pullback.snd G.hom (Out.jK R ≫ t)) (pullback.snd G.hom t) (Out.jK R) := by
    refine IsPullback.of_right ?_ hc₂ (IsPullback.of_hasPullback G.hom t)
    rw [hc₁]
    exact IsPullback.of_hasPullback G.hom (Out.jK R ≫ t)
  have : QuasiCompact c := MorphismProperty.of_isPullback sq.flip ‹_›
  have : IsSchemeTheoreticallyDominant c := .of_isPullback sq.flip
  refine ⟨g, hg, GlobalTheory.DedekindExt.Agree.of_dominant G.hom H.hom hf₀ hg c fun T u u' e => ?_⟩
  have h₁ := hA T (u ≫ c) u (by rw [Category.assoc, hc₁])
  have hu : u' = u ≫ a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k := by
    rw [← cancel_mono (pullback.fst G.hom j), ← e, Category.assoc, Category.assoc, hc₁, ← hρ, Category.assoc]
  rw [hu, ← Category.assoc, h₁, hK, Category.assoc, Category.assoc, Category.assoc]

theorem exists_agree_at_stalk : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  intro U S j _ G H _ _ hG hH f hf s i₁ i₂ i₃ k hk
  haveI := i₁; haveI := i₂; haveI := i₃
  exact @exists_agree_of_generic U S j _ G H _ _ hG hH f hf (S.presheaf.stalk s) _ i₁ i₂ i₃ (S.fromSpecStalk s) _ k hk

end GlobalTheory.StalkExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N 0 R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f :=
    fun a c σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hpH, hpn⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (-1) b t htH N
  have e1 : (N : ℤ) + N * -1 = 0 := by ring
  have e2 : (0 : ℤ) + N * b = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N 0 R, f * t ^ N ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH, hn⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P N 0 (N * -1) (N * b) f (t ^ N) hfH hpH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hpn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    exact (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
  have hinj : Set.InjOn (fun f => f * t ^ N) (P.Bl N 0 R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) h
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N 0 R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hX P b s t hG
  have hRep : P.Rep 0 (b : ℤ) (P.A.pow b) := by
    have := _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 0 1 P.A b (_root_.GlobalTheory.VolBr.Pair.rep_base k X p P).2.1
    simpa using this
  have hnef : (P.A.pow b).IsNef D := _root_.GlobalTheory.NefPow.isNef_pow hAC k X p D hX P.A b hG.nef
  have hnef0 : ((P.A.pow b).shift (fun _ => (0 : ℝ)) fun _ => rfl).IsNef D :=
    _root_.GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX (P.A.pow b) 0 le_rfl hnef
  obtain ⟨Φ, hΦ⟩ := ((hAC.arExists k X p D hX).2 Unit (fun _ => P.A.pow b)).1
  have hα := ((hAC.arIso k X p D hX).2 Unit (fun _ => P.A.pow b) Φ hΦ).1 ()
  have hlim := _root_.GlobalTheory.VolBr.lc_tendsto_of_rep hHS hAC k X p D hX P 0 b (P.A.pow b) _ 0 hRep hα hnef0 3 (by norm_num)
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      P.lc ((m : ℤ) * 0) ((m : ℤ) * b) (Real.exp (3 * m)) / (m : ℝ) ^ (D + 1) < C :=
    ⟨_, hlim.eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  rw [div_lt_iff₀ hpos] at hN
  simp only [mul_zero] at hN
  refine le_trans ?_ hN.le
  exact lc_le_of_good P hG N _ (_root_.GlobalTheory.VolBr.BallFinite.bl_finite hHS k X p D hX P b s t hG 0 _ _ hAC)

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_two_le_lc_one_add (hHS : GlobalTheory.Published.ArithHilbertSamuel) (hA : GlobalTheory.Published.ArCalc) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (b : ℕ)
    (s t : X.functionField) (hG : P.Good D b s t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  obtain ⟨h, hh⟩ := (hA.1 k X p D hX).1 P.A
  have hα : P.A.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
  have hnef := _root_.GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A 0 le_rfl hG.nef
  have hrep : P.Rep 0 1 P.A := (_root_.GlobalTheory.VolBr.Pair.rep_base k X p P).2.1
  have key := GlobalTheory.eventually_le_of_poly_asymptotics (D + 1) b
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 (j : ℤ) 2)
    (h (genericPoint X) / (D + 1).factorial) ((D + 1) * gdeg P.A D / (D + 1).factorial) (Nat.succ_pos D) hG.pos
    (fun η hη => by
      have := _root_.GlobalTheory.VolBr.lc_tendsto_of_rep hHS hA k X p D hX P 0 1 P.A (h (genericPoint X)) 0 hrep hα hnef η hη
      simpa only [mul_zero, mul_one] using this)
    (fun η hη => by
      have h1 : ∀ᶠ j : ℕ in atTop, Real.log 2 ≤ η * j :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
      filter_upwards [h1] with j hj
      have h2 : (2 : ℝ) ≤ Real.exp (η * j) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.2 hj
      have hsub : P.Bl 0 (j : ℤ) 2 ⊆ P.Bl 0 (j : ℤ) (Real.exp (η * j)) :=
        fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h2⟩
      have hfin := _root_.GlobalTheory.VolBr.BallFinite.bl_finite hHS k X p D hX P b s t hG 0 (j : ℤ) (Real.exp (η * j)) hA
      have hle := Set.ncard_le_ncard hsub hfin
      simp only [Pair.lc]
      rcases Nat.eq_zero_or_pos (P.Bl 0 (j : ℤ) 2).ncard with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle))
    ε hε
  filter_upwards [key] with n hn
  filter_upwards [hn] with m hm
  have e1 : (((b * n + 1) * m : ℕ) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) + (m : ℤ) := by push_cast; ring
  have e2 : (((b * n * m : ℕ)) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) := by push_cast; ring
  simp only [e1, e2, zero_mul, Real.exp_zero] at hm
  exact hm

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfForallField
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)

namespace GlobalTheory.FibreDim

theorem smoothOfRelativeDimension_of_forall_field : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (g : ℕ), Smooth X.hom → (∀ (k : Type) [Field k] [Algebra R k], SmoothOfRelativeDimension g (Limits.pullback.snd X.hom (spMap (algebraMap R k)))) → SmoothOfRelativeDimension g X.hom := by
  intro R _ X g hs h
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have hn : ∀ x, n x = g := fun x => by
    let p : PrimeSpectrum R := X.hom x
    have hk := h p.asIdeal.ResidueField
    let t := spMap (algebraMap R p.asIdeal.ResidueField)
    obtain ⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      exact Ideal.ker_algebraMap_residueField p.asIdeal
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)
    have h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) :=
      this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)
    have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) := by
      rw [← Limits.pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t)
      ⟨x, hW x⟩ y hy.symm
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FibreDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem Data.sec_smooth (D : Data) (U : D.X.affineOpens) : Algebra.Smooth D.R (Sec D.s U.1) := by
  haveI := D.smooth
  have h := HasRingHomProperty.appLE @Smooth D.s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((D.s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of D.R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of D.R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

theorem Data.mono_i (D : Data) : Mono D.i := by
  obtain ⟨s₀, hpb, -⟩ := D.red
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk D.I)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion D.i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip ‹_›
  infer_instance

theorem Data.affine_inf (D : Data) {U V : D.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := by
  haveI := D.sep
  haveI : IsSeparated (Limits.terminal.from D.X) := by
    rw [← Limits.terminal.comp_from D.s]; infer_instance
  exact hU.inf hV

theorem Data.smooth_mono_inf : ∀ D : Data, (∀ U : D.X.affineOpens, Algebra.Smooth D.R (Sec D.s U.1)) ∧ Mono D.i ∧
    ∀ U V : D.X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
  fun D ↦ ⟨D.sec_smooth, D.mono_i, fun _ _ hU hV ↦ D.affine_inf hU hV⟩

end GlobalTheory.SmoothLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySecondDifferenceEqCubicalRatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ = val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  first | exact @GlobalTheory.PolDeg.SymCube.sym_cube | exact GlobalTheory.PolDeg.SymCube.sym_cube | (intros; apply GlobalTheory.PolDeg.SymCube.sym_cube <;> assumption)
end

