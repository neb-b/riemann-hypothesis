module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushout
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FlatPinch

theorem surjective_fst_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) (hg₂ : Function.Surjective g₂) :
    Function.Surjective f₁ := by
  intro r
  obtain ⟨s, hs⟩ := hg₂ (g₁ r)
  obtain ⟨a, ha, -⟩ := (GlobalTheory.DualOpen.elem_of_isPullback_ring hP).2 r s hs.symm
  exact ⟨a, ha⟩

end GlobalTheory.FlatPinch

namespace GlobalTheory.FlatPinch

theorem resLE_homOfLE {Y' T X : Scheme.{0}} (f' : Y' ⟶ T) {V V' : T.Opens} (h : V' ≤ V) (g : V.toScheme ⟶ X)
    (w : Y' ⟶ X) (hg : f'.resLE V _ le_rfl ≫ g = (f' ⁻¹ᵁ V).ι ≫ w) :
    f'.resLE V' _ le_rfl ≫ T.homOfLE h ≫ g = (f' ⁻¹ᵁ V').ι ≫ w := by
  have e : f'.resLE V' _ le_rfl ≫ T.homOfLE h = Y'.homOfLE (f'.preimage_mono h) ≫ f'.resLE V _ le_rfl := by
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
  rw [reassoc_of% e, hg, Scheme.homOfLE_ι_assoc]

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hfl h₁ h₂ h₀ hij hp₂
  have hf₁ : Function.Surjective f₁ := surjective_fst_of_isPullback hP hg₂
  have hf₂ : Function.Surjective f₂ := surjective_fst_of_isPullback hP.flip hg₁
  haveI : IsClosedImmersion j₁ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₁.flip (IsClosedImmersion.spec_of_surjective f₁ hf₁)
  haveI : IsClosedImmersion j₂ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₂.flip (IsClosedImmersion.spec_of_surjective f₂ hf₂)
  obtain ⟨hcov, hpts⟩ := _root_.GlobalTheory.PinchPoints.points_of_pinch _ _ _ _ _ _ _ _ hP hloc hart hg₁ hg₂ _ _ _ _ Y.hom Y₁.hom Y₂.hom Y₀.hom
    j₁ j₂ i₁ i₂ h₁ h₂ h₀ hij
  have hM : GlobalTheory.DualOpen.Milnor (Spec.map f₂) (Spec.map f₁) (Spec.map g₂) (Spec.map g₁) :=
    GlobalTheory.DualOpen.Milnor.of_isPullback hP.flip hg₁
  haveI : Flat Y.hom := hfl
  have SEC := fun W => GlobalTheory.DualOpen.sections_of_squares hM h₂ h₁ h₀ hij.symm hp₂ W
  have hinj : ∀ (W : Y.left.Opens) (a b : Γ(Y.left, W)), j₁.app W a = j₁.app W b → j₂.app W a = j₂.app W b → a = b :=
    fun W a b e1 e2 => (SEC W).1 a b e2 e1
  have uniqV := fun (X : Scheme.{0}) (V : Y.left.Opens) =>
    _root_.GlobalTheory.scheme_hom_ext_of_jointly_injective _ _ _ X _ _ ((_root_.GlobalTheory.cover_and_joint_inj_restrict _ _ _ j₁ j₂ hcov hinj V).1)
      ((_root_.GlobalTheory.cover_and_joint_inj_restrict _ _ _ j₁ j₂ hcov hinj V).2)
  have uniq : ∀ (X : Scheme.{0}) (a b : Y.left ⟶ X), j₁ ≫ a = j₁ ≫ b → j₂ ≫ a = j₂ ≫ b → a = b :=
    fun X => _root_.GlobalTheory.scheme_hom_ext_of_jointly_injective _ _ _ X j₁ j₂ hcov hinj
  have key : ∀ (X : Scheme.{0}) (a₁ : Y₁.left ⟶ X) (a₂ : Y₂.left ⟶ X), i₁ ≫ a₁ = i₂ ≫ a₂ →
      ∃ a : Y.left ⟶ X, j₁ ≫ a = a₁ ∧ j₂ ≫ a = a₂ := by
    intro X a₁ a₂ ha
    have hpa : ∀ (y₁ : Y₁.left) (y₂ : Y₂.left), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂ := by
      intro y₁ y₂ h
      obtain ⟨y₀, rfl, rfl⟩ := hpts y₁ y₂ h
      have := congrArg (fun q : Y₀.left ⟶ X => q y₀) ha
      simpa using this
    have hloc := _root_.GlobalTheory.closedCover_affine_nbhd_maps_into_affine _ _ _ X j₁ j₂ a₁ a₂ hcov hpa
    let Idx := {p : Y.left.Opens × X.affineOpens //
      IsAffineOpen p.1 ∧ j₁ ⁻¹ᵁ p.1 ≤ a₁ ⁻¹ᵁ p.2.1 ∧ j₂ ⁻¹ᵁ p.1 ≤ a₂ ⁻¹ᵁ p.2.1}
    have hcovI : TopologicalSpace.IsOpenCover (fun p : Idx => p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro y _
      obtain ⟨W, U, hW, hy, h1, h2⟩ := hloc y
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(W, U), hW, h1, h2⟩, hy⟩
    have EO : ∀ p : Idx, ∃ g : p.1.1.toScheme ⟶ X, j₁.resLE _ _ le_rfl ≫ g = (j₁ ⁻¹ᵁ p.1.1).ι ≫ a₁ ∧
        j₂.resLE _ _ le_rfl ≫ g = (j₂ ⁻¹ᵁ p.1.1).ι ≫ a₂ := by
      rintro ⟨⟨W, U⟩, hW, hx, hz⟩
      have hW1 : IsAffineOpen (j₁ ⁻¹ᵁ W) := hW.preimage j₁
      have hW2 : IsAffineOpen (j₂ ⁻¹ᵁ W) := hW.preimage j₂
      have hpre : i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W) = i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ W) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hij]
      refine GlobalTheory.Pinch.exists_glue_of_sections j₁ j₂ W hW hW1 hW2 U a₁ a₂ hx hz ?_ ?_
      · intro t₁ t₂ e1 e2
        rw [← Scheme.Hom.app_eq_appLE] at e1 e2
        exact hinj W t₁ t₂ e1 e2
      · intro u
        obtain ⟨t, ht2, ht1⟩ := (SEC W).2 (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) le_rfl hpre.le le_rfl
          (a₂.appLE U.1 _ hz u) (a₁.appLE U.1 _ hx u) (by
            have e1 := Scheme.Hom.appLE_comp_appLE i₂ a₂ U.1 _ (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) hz le_rfl
            have e2 := Scheme.Hom.appLE_comp_appLE i₁ a₁ U.1 _ (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) hx hpre.le
            have e3 := GlobalTheory.Pinch.appLE_congr_hom ha.symm U.1 (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W))
              (fun w hw => hz hw) (fun w hw => hx (hpre.le hw))
            have := congrArg (fun q => q.hom u) (e1.trans (e3.trans e2.symm))
            simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
            exact this)
        refine ⟨t, ?_, ?_⟩
        · rw [← Scheme.Hom.app_eq_appLE]; exact ht1
        · rw [← Scheme.Hom.app_eq_appLE]; exact ht2
    let 𝒰 := Y.left.openCoverOfIsOpenCover _ hcovI
    choose g hg using EO
    have hc : ∀ a b : Idx, pullback.fst (𝒰.f a) (𝒰.f b) ≫ g a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ g b := by
      intro a b
      have hPb := isPullback_opens_inf a.1.1 b.1.1
      change pullback.fst a.1.1.ι b.1.1.ι ≫ g a = pullback.snd a.1.1.ι b.1.1.ι ≫ g b
      rw [← cancel_epi hPb.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc]
      refine uniqV X (a.1.1 ⊓ b.1.1) _ _ ?_ ?_
      · rw [resLE_homOfLE j₁ _ _ a₁ (hg a).1, resLE_homOfLE j₁ _ _ a₁ (hg b).1]
      · rw [resLE_homOfLE j₂ _ _ a₂ (hg a).2, resLE_homOfLE j₂ _ _ a₂ (hg b).2]
    let z₀ := 𝒰.glueMorphisms g hc
    have hz₀ : ∀ a : Idx, a.1.1.ι ≫ z₀ = g a := fun a => 𝒰.ι_glueMorphisms g hc a
    refine ⟨z₀, ?_, ?_⟩
    · have hcov1 : TopologicalSpace.IsOpenCover (fun p : Idx => j₁ ⁻¹ᵁ p.1.1) := by
        rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcovI, Scheme.Hom.preimage_top]
      refine Scheme.Cover.hom_ext (Y₁.left.openCoverOfIsOpenCover _ hcov1) _ _ fun a => ?_
      change (j₁ ⁻¹ᵁ a.1.1).ι ≫ j₁ ≫ z₀ = (j₁ ⁻¹ᵁ a.1.1).ι ≫ a₁
      rw [← (hg a).1, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j₁ (le_rfl), Category.assoc]
    · have hcov2 : TopologicalSpace.IsOpenCover (fun p : Idx => j₂ ⁻¹ᵁ p.1.1) := by
        rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcovI, Scheme.Hom.preimage_top]
      refine Scheme.Cover.hom_ext (Y₂.left.openCoverOfIsOpenCover _ hcov2) _ _ fun a => ?_
      change (j₂ ⁻¹ᵁ a.1.1).ι ≫ j₂ ≫ z₀ = (j₂ ⁻¹ᵁ a.1.1).ι ≫ a₂
      rw [← (hg a).2, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j₂ (le_rfl), Category.assoc]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk j₁ j₂ hij)
    (PushoutCocone.IsColimit.mk _ (fun s => Classical.choose (key _ s.inl s.inr s.condition))
      (fun s => (Classical.choose_spec (key _ s.inl s.inr s.condition)).1)
      (fun s => (Classical.choose_spec (key _ s.inl s.inr s.condition)).2)
      (fun s m e1 e2 => uniq _ _ _ (e1.trans (Classical.choose_spec (key _ s.inl s.inr s.condition)).1.symm)
        (e2.trans (Classical.choose_spec (key _ s.inl s.inr s.condition)).2.symm)))

end GlobalTheory.FlatPinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZero
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechDR KaehlerDifferential
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanVanish

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem snd_val_affine {R' : Type} [CommRing R'] [Algebra R R'] (U : X.affineOpens)
    (α : Sec s U.1 →ₐ[R] TrivSqZeroExt R' R') (y : Sp (TrivSqZeroExt R' R') ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : spMap (α : Sec s U.1 →+* TrivSqZeroExt R' R') ≫ affPt s U = y) (f : Form s)
    (h0 : connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) = 0 := by
  have hx := affPt_w s U
  letI : Algebra (Sec s U.1) R' := ((TrivSqZeroExt.fstHom R R' R').comp α).toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec s U.1) R' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg TrivSqZeroExt.fst (α.commutes r)).symm
  let δ : Derivation R (Sec s U.1) R' :=
    { toFun := fun b ↦ (α b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  let δ' := δ.liftKaehlerDifferential
  have hop : ∀ (b : Sec s U.1) (ω : Ω[Sec s U.1⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
  let Φ : TrivSqZeroExt (Sec s U.1) Ω[Sec s U.1⁄R] →ₐ[R] TrivSqZeroExt R' R' :=
    { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap (Sec s U.1) R' c.fst) +
        TrivSqZeroExt.inr (δ' c.snd)
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b ↦ by ext <;> simp <;> ring
      map_mul' := fun a b ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, hop, map_add (f := _), map_smul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul, Algebra.smul_def]
          simp [MulOpposite.smul_eq_mul_unop]
          ring
      commutes' := fun r ↦ by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply] }
  let α₀ : Sec s U.1 →ₐ[R] R' := (TrivSqZeroExt.fstHom R R' R').comp α
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R R' R').π (Φ c) := fun c ↦ by
    simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have e₀ : spMap (α₀ : Sec s U.1 →+* R') ≫ affPt s U =
      spMap ((SqExt.ofModule R R' R').π : TrivSqZeroExt R' R' →+* R') ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]; rfl
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R R' R') Φ α₀ hπ hx
    ((SqExt.ofModule R R' R').red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv R' _ ((SqExt.ofModule R R' R').red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt R' R') y hy :=
    Thick.trivHom α e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R R' R').secHom ((SqExt.ofModule R R' R').red_w hy)
    (SqExt.ofModule R R' R').i (SqExt.ofModule R R' R').π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext <;> simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R R' R').idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl fun c ↦ by
      change α c = Φ (diagSec R (Sec s U.1) c)
      ext
      · simp [Φ, RingHom.algebraMap_toAlgebra]
      · simp only [Φ, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, snd_derSec]
        exact (Derivation.liftKaehlerDifferential_comp_D δ c).symm
  have hΦ : ∀ z, TrivSqZeroExt.snd (Φ z) = δ' z.snd := fun z ↦ by simp [Φ]
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = 0
  rw [← map_sub, hΦ]
  have h0' : TrivSqZeroExt.snd (ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i
      fun _ ↦ rfl) - ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1))
      (fst_derSec _))) = 0 := h0
  rw [h0', map_zero]

theorem snd_val_eq_zero (y : Sp (DualNumber R) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber R))) (f : Form s)
    (h0 : ∀ U : X.affineOpens, connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
  have loc : ∀ m : Ideal R, m.IsMaximal →
      ∃ t ∉ m, t * TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
    intro m hm
    haveI := hm.isPrime
    let R' := Localization.AtPrime m
    haveI : IsLocalRing (TrivSqZeroExt R' R') :=
      IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun c ↦ by
        simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
        exact IsLocalRing.isUnit_or_isUnit_one_sub_self c.fst
    let φ : DualNumber R →ₐ[R] TrivSqZeroExt R' R' :=
      { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap R R' c.fst) +
          TrivSqZeroExt.inr (algebraMap R R' c.snd)
        map_one' := by ext <;> simp
        map_zero' := by ext <;> simp
        map_add' := fun a b ↦ by ext <;> simp [Algebra.smul_def] <;> ring
        map_mul' := fun a b ↦ by ext <;> simp [MulOpposite.smul_eq_mul_unop, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl'] <;> ring
        commutes' := fun r ↦ by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl'] }
    let y' := spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y
    have hy' : y' ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
      change (spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y) ≫ s = _
      rw [Category.assoc, hy, ← Cris.spMap_comp, φ.comp_algebraMap]
    have hv := (SqExt.dual R).val_map (SqExt.ofModule R R' R') φ (Algebra.ofId R R')
      (fun c ↦ by simp [φ]) (fun b ↦ by ext <;> simp [φ, TrivSqZeroExt.algebraMap_eq_inl']) y hy y' hy' rfl f
    obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
      (x := y' (IsLocalRing.closedPoint (TrivSqZeroExt R' R'))) trivial
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem y' hp
    let α₁ : Sec s U →+* TrivSqZeroExt R' R' := evalAt y' U htop.ge
    have hα : spMap α₁ ≫ affPt s ⟨U, hU⟩ = y' := by
      have k := IsAffineOpen.SpecMap_appLE_fromSpec y' hU (isAffineOpen_top _) htop.ge
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at k
      have e1 : spMap α₁ ≫ affPt s ⟨U, hU⟩ =
          Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R' R'))).hom) ≫
          Spec.map (y'.appLE U ⊤ htop.ge) ≫ hU.fromSpec := by
        rw [← Category.assoc, ← Spec.map_comp]; rfl
      rw [e1]
      rw [k]
      simp only [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    have hc : α₁.comp (algebraMap R (Sec s U)) = algebraMap R (TrivSqZeroExt R' R') := by
      have e2 : spMap (α₁.comp (algebraMap R (Sec s U))) = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
        rw [Cris.spMap_comp, ← affPt_w s ⟨U, hU⟩, ← Category.assoc, hα, hy']
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let α : Sec s U →ₐ[R] TrivSqZeroExt R' R' :=
      { α₁ with commutes' := fun r ↦ RingHom.congr_fun hc r }
    have h1 := snd_val_affine ⟨U, hU⟩ α y' hy' hα f (h0 _)
    rw [hv] at h1
    have h2 : algebraMap R R' (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)) = 0 := by
      simpa [φ, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl'] using h1
    obtain ⟨⟨t, ht⟩, ht'⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl R' _).1 h2
    exact ⟨t, ht, ht'⟩
  by_contra hx
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R
    (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)))
  have hJ : J ≠ ⊤ := fun h ↦ hx (by
    have : (1 : R) ∈ J := h ▸ Submodule.mem_top
    simpa [J] using this)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨t, ht, ht'⟩ := loc m hm
  exact ht (hJm (by simpa [J] using ht'))

theorem tanVal_eq_zero_of_cmpForm_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R))
    (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))),
    GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  intro R _ A v f hf
  rw [tanVal_apply]
  refine snd_val_eq_zero v.left (pt_w v) f fun U ↦ ?_
  have := congrArg (fun g : ClosedForm (A.hom ≫ 𝟙 (Sp R)) ↦ g.1.1 (Opposite.op U)) hf
  exact (cmpForm_apply _ f (Opposite.op U)).symm.trans (this.trans rfl)

end GlobalTheory.TanVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.alg_of_isProjBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsProjBy f → Alg f I := by
  intro R _ _ I hc W f hP t ht hp
  obtain ⟨q, β, hq, hβ, hpb⟩ := _root_.GlobalTheory.FormalAlg.isSystem_tower R I W f t ht
  let Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := fun e => Over.mk (q e)
  let j : ∀ e, (Y e).left ⟶ W := fun e => (t e).subschemeι
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  let t' := fun e => Classical.choose (GlobalTheory.MorAlg.exists_isPull (j e) hH s)
  have ht' : ∀ e, GlobalTheory.MorAlg.IsPull (j e) s (t' e) :=
    fun e => Classical.choose_spec (GlobalTheory.MorAlg.exists_isPull (j e) hH s)
  have hv : ∀ e, GlobalTheory.MorAlg.IsPull (β e) (t' (e + 1)) (t' e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hH (hL _) (hL _) (ht' (e + 1)) (by
      have h1 : β e ≫ j (e + 1) = j e := hβ e
      rw [h1]; exact ht' e)
  choose v hv cv using hv
  have hjR : ∀ e, j e ≫ f = (Y e).hom ≫ thick R I e := hq
  have hva : VeryAmpleBy (Y 0).hom (H.pull (j 0)) (t' 0) := by
    obtain ⟨w, hw, c⟩ := ht' 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R W f H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _ (hL 0) hw c
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (Y 0).hom (hjR 0) ≫ pullback.fst f (thick R I 0)) := by
      rw [pullback.lift_fst]
      exact inferInstanceAs (IsClosedImmersion (t 0).subschemeι)
    exact IsClosedImmersion.of_comp _ (pullback.fst f (thick R I 0))
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := _root_.GlobalTheory.FormalAlg.exists_projective_of_formal_embedding R I hc Y β hpb (fun e => H.pull (j e)) v
    (fun e => ⟨hL e, hv e⟩) n t' cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R W f H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => (mem_vanIdeal _ _ _).1 (heq d F hF fun e => (mem_vanIdeal _ _ _).2 fun k => by
      rw [← hjR]
      exact (ht' e).eqn f hH hF h0 k)
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := GlobalTheory.MorAlg.IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht' e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections R W f H n s hH hs _ _ (t' e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjR]
    exact (hb e).w
  haveI hci : IsClosedImmersion φ := _root_.GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat R W f H n s hH hs B.left B.hom H' s' φ u hH' hs' hφ hu cu
  haveI hBp : IsProper (φ ≫ f) := by
    rw [hφ]; exact GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩
  refine ⟨φ.ker, ?_, fun e => ?_⟩
  · change IsProper (φ.imageι ≫ f)
    have hg : φ.imageι = inv φ.toImage ≫ φ := (IsIso.eq_inv_comp _).2 φ.toImage_imageι
    rw [hg, Category.assoc]
    infer_instance
  · have key := (_root_.GlobalTheory.FormalAlg.reduces_iff_ker_eq R (I ^ (e + 1)) W B.left (Y e).left f φ (j e) (q e) hci
      (inferInstanceAs (IsClosedImmersion (t e).subschemeι)) (hq e)).1
      ⟨b e, hbφ e, by rw [hφ]; exact hb e⟩
    rw [key]
    exact Scheme.IdealSheafData.ker_subschemeι (t e)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyEtale_polynomialPlace_to_place : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  first | exact @GlobalTheory.FieldPair.formallyEtale_polyPlace | exact GlobalTheory.FieldPair.formallyEtale_polyPlace | (intros; apply GlobalTheory.FieldPair.formallyEtale_polyPlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.VPre

theorem four_rescale : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.Four N₁ → ∀ v : ∀ y, (Φ.V y)ˣ, (∀ e : ℕ, ∃ a : A, ∀ y, Φ.ev y a - ((v y)⁻¹ : (Φ.V y)ˣ) ∈ (maximalIdeal A ^ e).map (Φ.ev y)) → (Φ.rescale v).Four N₁ := by
  intro O _ bar q s W A _ _ Φ N₁ hF w hw (y₀ : Φ.Y) N₀
  obtain ⟨N, hN0, hN1, k, hk0, hku, hmain⟩ := hF y₀ N₀
  refine ⟨N, hN0, hN1, k, hk0, hku, ?_⟩
  intro l a c e
  obtain ⟨f, hf⟩ := hmain l a c e
  obtain ⟨b, hb⟩ := hw (e + 1)

  have hmax : ∀ (y : Φ.Y) (x : A), x ∈ maximalIdeal A → Φ.ev y x ∈ maximalIdeal (Φ.V y) := by
    intro y x hx
    haveI := Φ.ev_loc y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hx) (isUnit_of_map_unit (Φ.ev y) x hu)
  have hle : ∀ y : Φ.Y, (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ maximalIdeal (Φ.V y) := by
    intro y
    rw [Ideal.map_le_iff_le_comap]
    exact le_trans (Ideal.pow_le_self (Nat.succ_ne_zero e)) (fun x hx => hmax y x hx)
  have hbu : IsUnit b := by
    by_contra hn
    have hbm : b ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have h1 : Φ.ev y₀ b ∈ maximalIdeal (Φ.V y₀) := hmax y₀ b hbm
    have h2 := hle y₀ (hb y₀)
    have h3 : (((w y₀)⁻¹ : (Φ.V y₀)ˣ) : Φ.V y₀) ∈ maximalIdeal (Φ.V y₀) := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp h3) (Units.isUnit _)
  refine ⟨f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l, fun (y : Φ.Y) j => ?_⟩
  obtain ⟨S, hS1, hS2, hS3⟩ := hf y j
  refine ⟨S, hS1, hS2, ?_⟩
  set J := maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) with hJ
  have hIe : (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ J :=
    le_trans (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ e))) le_sup_right
  set z : Φ.V y := Φ.ev y ((hbu.unit⁻¹ : Aˣ) : A) with hz
  set ww : Φ.V y := ((w y : (Φ.V y)ˣ) : Φ.V y) with hww
  have hzb : z * Φ.ev y b = 1 := by
    rw [hz, ← map_mul]
    simp
  have hzw : z - ww ∈ J := by
    apply hIe
    have h := (hb y)
    have hx : z - ww = -(z * ww * (Φ.ev y b - (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y))) := by
      have : ww * (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y) = 1 := by simp [hww]
      linear_combination ww * hzb - z * this
    rw [hx]
    exact neg_mem (Ideal.mul_mem_left _ _ h)
  have hprod : ∀ mu : Fin l × Fin s → Φ.X y,
      (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = (∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww ^ l := by
    intro mu
    rw [show (fun i => Φ.u y (fun x => mu (i, x)) (c i) * ww * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = fun i => (Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww from
        funext fun i => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  show Φ.ev y (f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l) - ∑ mu ∈ S, (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) ∈ J
  simp_rw [hprod]
  rw [← Finset.sum_mul, map_mul, map_pow, ← hz]
  set P := ∑ mu ∈ S, ∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))
  have hd : z ^ l - ww ^ l ∈ J := by
    obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow z ww l
    rw [hr]
    exact Ideal.mul_mem_right _ _ hzw
  have : Φ.ev y f * z ^ l - P * ww ^ l = z ^ l * (Φ.ev y f - P) + P * (z ^ l - ww ^ l) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS3) (Ideal.mul_mem_left _ _ hd)

end GlobalTheory.Poinc.VPre
end

