module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericExt

universe u

theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem exists_hom_specStalk {W Y T X : Scheme.{u}} (j : W ⟶ Y) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] [X.IsSeparated] (F : W ⟶ X) (g' : T ⟶ Y) [Flat g'] (g : T ⟶ X)
    (H : ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) (p : T) :
    ∃ φ : Spec (Y.presheaf.stalk (g' p)) ⟶ X, ∀ (Z : Scheme.{u})
      (ρ : Z ⟶ Spec (Y.presheaf.stalk (g' p))) (r : Z ⟶ W),
      r ≫ j = ρ ≫ Y.fromSpecStalk (g' p) → r ≫ F = ρ ≫ φ := by
  let h := Spec.map (g'.stalkMap p)
  obtain ⟨h₁, h₂⟩ : Flat h ∧ Surjective h :=
    (flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_stalkMap_of_flat g' p)
  have hh : h ≫ Y.fromSpecStalk (g' p) = T.fromSpecStalk p ≫ g' :=
    Scheme.SpecMap_stalkMap_fromSpecStalk g'
  have := flat_fromSpecStalk Y (g' p)
  have key : pullback.fst h h ≫ T.fromSpecStalk p ≫ g = pullback.snd h h ≫ T.fromSpecStalk p ≫ g := by
    let q := pullback.fst h h ≫ h ≫ Y.fromSpecStalk (g' p)
    have hq : Flat q := inferInstance
    refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst q j) (terminal.from X) ?_
      (terminal.hom_ext _ _)
    have e₁ := H _ (pullback.fst q j ≫ pullback.fst h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]; simp only [q, Category.assoc, hh])
    have e₂ := H _ (pullback.fst q j ≫ pullback.snd h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]
      simp only [q, Category.assoc, ← hh, pullback.condition_assoc])
    simpa only [Category.assoc] using e₁.symm.trans e₂
  let φ := EffectiveEpi.desc h (T.fromSpecStalk p ≫ g) (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hφ : h ≫ φ = T.fromSpecStalk p ≫ g := EffectiveEpi.fac _ _ _
  refine ⟨φ, fun Z ρ r hr => ?_⟩
  rw [← cancel_epi (pullback.fst ρ h), pullback.condition_assoc, hφ]
  have := H _ (pullback.snd ρ h ≫ T.fromSpecStalk p) (pullback.fst ρ h ≫ r) (by
    rw [Category.assoc, hr, pullback.condition_assoc, hh, Category.assoc])
  simpa only [Category.assoc] using this

theorem exists_extension {W Y X S : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j] [IsIntegral Y] [S.IsSeparated] (sY : Y ⟶ S) (sX : X ⟶ S) [IsSeparated sX]
    [LocallyOfFiniteType sX] (F : W ⟶ X) (hF : F ≫ sX = j ≫ sY)
    (H : ∀ y : Y, y ∉ Set.range j → ∃ (T : Scheme.{u}) (g' : T ⟶ Y) (g : T ⟶ X), Flat g' ∧ y ∈ Set.range g' ∧
      ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) :
    ∃ ψ : Y ⟶ X, j ≫ ψ = F ∧ ψ ≫ sX = sY := by
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  let e₀ := Y.fromSpecStalk (genericPoint Y)
  have : IsDominant e₀ := isDominant_fromSpecStalk_genericPoint Y
  have hr : Set.range e₀ ⊆ Set.range j := by
    rw [Scheme.range_fromSpecStalk]
    intro z hz
    have hg : genericPoint Y ∈ Set.range j :=
      (genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range |>.2
        (by simpa [Set.range_nonempty_iff_nonempty] using j.denseRange.nonempty)
    exact Specializes.mem_open hz j.isOpenEmbedding.isOpen_range hg
  let e := IsOpenImmersion.lift j e₀ hr
  have he : e ≫ j = e₀ := IsOpenImmersion.lift_fac _ _ _
  have loc : ∀ y : Y, ∃ (U : Scheme.{u}) (k : U ⟶ Y) (_ : IsOpenImmersion k) (ψ : U ⟶ X)
      (l : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ U),
      y ∈ Set.range k ∧ l ≫ k = e₀ ∧ l ≫ ψ = e ≫ F := by
    intro y
    by_cases hy : y ∈ Set.range j
    · exact ⟨W, j, inferInstance, F, e, hy, he, rfl⟩
    obtain ⟨T, g', g, hg', ⟨p, rfl⟩, hT⟩ := H y hy
    obtain ⟨φ, hφ⟩ := exists_hom_specStalk j F g' g hT p
    have := flat_fromSpecStalk Y (g' p)
    have hover : φ ≫ sX = Y.fromSpecStalk (g' p) ≫ sY := by
      refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst (Y.fromSpecStalk (g' p)) j)
        (terminal.from S) ?_ (terminal.hom_ext _ _)
      rw [← reassoc_of% (hφ _ _ _ pullback.condition.symm), hF, pullback.condition_assoc]
    obtain ⟨U, hU, ψ, h₁, -⟩ := spread_out_of_isGermInjective' sY sX φ hover
    let m := Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (g' p)))
    have hm : m ≫ Y.fromSpecStalk (g' p) = e₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    refine ⟨U, U.ι, inferInstance, ψ, m ≫ U.fromSpecStalkOfMem _ hU, ⟨⟨_, hU⟩, rfl⟩, ?_, ?_⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hm]
    · rw [Category.assoc, ← h₁]
      exact (hφ _ m e (he.trans hm.symm)).symm
  choose U k hk ψ l hy hl hψ using loc
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y U k (fun y => ⟨y, hy y⟩) hk
  have hc : ∀ a b : Y, pullback.fst (k a) (k b) ≫ ψ a = pullback.snd (k a) (k b) ≫ ψ b := by
    intro a b
    let m := pullback.lift (l a) (l b) ((hl a).trans (hl b).symm)
    have : IsReduced (pullback (k a) (k b)) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ k a)
    have : IsDominant (m ≫ pullback.fst _ _ ≫ k a) := by
      rw [pullback.lift_fst_assoc, hl]
      infer_instance
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ k a)
    refine ext_of_isDominant m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hψ, hψ]
  have hι : ∀ a : Y, k a ≫ 𝒰.glueMorphisms ψ hc = ψ a := fun a => 𝒰.ι_glueMorphisms ψ hc a
  have h1 : j ≫ 𝒰.glueMorphisms ψ hc = F := by
    have : IsReduced W := isReduced_of_isOpenImmersion j
    have : IsDominant (e ≫ j) := by rw [he]; infer_instance
    have : IsDominant e := .of_comp_of_isOpenImmersion e j
    refine ext_of_isDominant e ?_
    rw [reassoc_of% he, ← hl (genericPoint Y), Category.assoc, hι, hψ]
  refine ⟨_, h1, ext_of_isDominant j ?_⟩
  rw [reassoc_of% h1, hF]

theorem isOpenImmersion_jK (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion (jK R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem eq_closedPoint_of_not_mem_range (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (s : Spec (CommRingCat.of R)) (hs : s ∉ Set.range (jK R)) : s = IsLocalRing.closedPoint R := by
  by_cases h : s.asIdeal = ⊥
  · refine (hs ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩).elim
    rw [h]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (s.isPrime.isMaximal h))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X' X : Over (Spec (CommRingCat.of R))) [Flat X'.hom] [IsIntegral X'.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] (f : (Over.pullback (jK R)).obj X' ⟶ (Over.pullback (jK R)).obj X), (∀ x : X'.left, X'.hom x = IsLocalRing.closedPoint R → ∃ (T : Scheme.{0}) (g' : T ⟶ X'.left) (g : T ⟶ X.left), Flat g' ∧ x ∈ Set.range g' ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj X').left), r ≫ pullback.fst X'.hom (jK R) = ρ ≫ g' → r ≫ f.left ≫ pullback.fst X.hom (jK R) = ρ ≫ g) → ∃ ψ : X' ⟶ X, (Over.pullback (jK R)).map ψ = f := by
  intro R _ _ _ X' X _ _ _ _ f H
  have := isOpenImmersion_jK R
  have : IsDominant (jK R) := DVR.isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsDominant (pullback.fst X'.hom (jK R)) := inferInstance
  have hf : f.left ≫ pullback.snd X.hom (jK R) = pullback.snd X'.hom (jK R) := Over.w f
  obtain ⟨ψ, h₁, h₂⟩ := exists_extension (pullback.fst X'.hom (jK R)) X'.hom X.hom
    (f.left ≫ pullback.fst X.hom (jK R))
    (by rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]; congr 1)
    (fun y hy => H y (eq_closedPoint_of_not_mem_range R _ fun h => hy (by
      rw [Scheme.Pullback.range_fst]; exact h)))
  refine ⟨Over.homMk ψ h₂, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
  · exact (pullback.lift_fst _ _ _).trans h₁
  · exact (Over.w _).trans hf.symm

end GlobalTheory.GenericExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfGroupLike
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.UnitRigid

theorem coeff_inl_mul_inr {B X : Type} [CommRing B] [AddCommGroup X] (a b : AddMonoidAlgebra B X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) a *
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) b).coeff (x, y) = a.coeff x * b.coeff y := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' h h' => simp only [map_add (f := _), add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
  | single p r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' h h' => simp only [map_add (f := _), mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
    | single q s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h₁ : p = x <;> by_cases h₂ : q = y <;> simp [h₁, h₂]

theorem eq_one_of_groupLike {B X : Type} [CommRing B] [AddCommGroup X] (I : Ideal B) (hI : ∀ b ∈ I, IsNilpotent b)
    (g : AddMonoidAlgebra B X)
    (h : AddMonoidAlgebra.mapDomainRingHom B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) g =
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) g *
        AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) g)
    (h₁ : AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I) g = 1) : g = 1 := by
  classical
  have idem : ∀ x, IsIdempotentElem (g.coeff x) := fun x => by
    have e := congrArg (fun a => a.coeff (x, x)) h
    simp only [coeff_inl_mul_inr] at e
    refine e.symm.trans ?_
    exact Finsupp.mapDomain_apply_of_injective (f := fun x : X => (x, x)) (fun _ _ q => congrArg Prod.fst q) g.coeff x
  ext x
  have e := congrArg (fun a => a.coeff x) h₁
  simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at e ⊢
  split_ifs at e ⊢ with hx
  · have m : 1 - g.coeff x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self]
    exact (sub_eq_zero.1 ((idem x).one_sub.eq_zero_of_isNilpotent (hI _ m))).symm
  · exact (idem x).eq_zero_of_isNilpotent (hI _ (Ideal.Quotient.eq_zero_iff_mem.1 e))

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem point_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

theorem exists_point (Z : Over S) (c : Multiplicative X →* Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, ∀ χ, (chV t χ).val = c (Multiplicative.ofAdd χ) :=
  ⟨(splitTorusPointsEquiv S X Z).symm c.toHomUnits, fun χ => by rw [chV, MulEquiv.apply_symm_apply]; rfl⟩

theorem exists_universal {Y W : Over S} [IsAffine W.left] (y : W ⟶ Y) (u : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ g : AddMonoidAlgebra Γ(W.left, ⊤) X, ∀ (Z : Over S) (s : Z ⟶ W) (t : Z ⟶ splitTorus S X)
      (θ : AddMonoidAlgebra Γ(W.left, ⊤) X →+* Γ(Z.left, ⊤)),
      (∀ b, θ (AddMonoidAlgebra.single 0 b) = s.left.appTop.hom b) →
      (∀ χ, θ (AddMonoidAlgebra.single χ 1) = (chV t χ).val) → (lift t (s ≫ y)).left.appTop.hom u = θ g := by
  obtain ⟨U, y₀, e, -, -, H⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) X)
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, ht₀⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
  refine ⟨e ((lift t₀ (y₀ ≫ y)).left.appTop.hom u), fun Z s t θ h₁ h₂ => ?_⟩
  obtain ⟨σ, hσ, hθ⟩ := H Z s θ h₁
  have ht : σ ≫ t₀ = t := point_ext fun χ => by
    rw [chV_comp, hθ, ht₀, ← h₂]
    exact congrArg θ (e.apply_symm_apply _)
  rw [← hθ, ← ht, ← hσ, Category.assoc, ← comp_lift, Rosenlicht.over_appTop_comp]

theorem eq_one_affine {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) {Y W : Over (Spec (CommRingCat.of A))}
    [IsAffine W.left] (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤))
    (hm : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u = (lift t y).left.appTop.hom u * (lift t' y).left.appTop.hom u)
    (h₁ : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift t y).left.appTop.hom u = 1) (t : W ⟶ splitTorus _ X) (y : W ⟶ Y) : (lift t y).left.appTop.hom u = 1 := by
  obtain ⟨g, hg⟩ := exists_universal y u
  let I : Ideal Γ(W.left, ⊤) := J.map (RingPoint.strMap W)
  have hI : ∀ b ∈ I, IsNilpotent b := fun b hb => by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hb n
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot] at this
    exact this
  have one : g = 1 := by
    refine eq_one_of_groupLike I hI g ?_ ?_
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) (X × X))
        AddMonoidAlgebra.singleZeroRingHom
      have key : ∀ (f : X →+ X × X) (t : U ⟶ splitTorus _ X),
          (∀ χ, (chV t χ).val = e.symm (AddMonoidAlgebra.single (f χ) 1)) →
          (lift t (s ≫ y)).left.appTop.hom u = e.symm (AddMonoidAlgebra.mapDomainRingHom _ f g) := fun f t ht =>
        hg U s t (e.symm.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom _ f))
          (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [ht]; simp)
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inl X X))))
      obtain ⟨t₂, ht₂⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr X X))))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inl X X χ) 1) := ht₁
      have a₂ : ∀ χ, (chV t₂ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inr X X χ) 1) := ht₂
      apply e.symm.injective
      rw [map_mul, ← key _ t₁ a₁, ← key _ t₂ a₂, ← hm, key]
      intro χ
      rw [chV_mul, Units.val_mul, a₁, a₂, ← map_mul, AddMonoidAlgebra.single_mul_single]
      simp
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra (Γ(W.left, ⊤) ⧸ I) X)
        (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single χ 1) := ht₁
      have hU : ∃ s, s ≫ red J = U.hom := (RingPoint.exists_comp_red_iff J U).2 fun a ha => by
        apply e.injective
        rw [← RingPoint.appTop_strMap s, he, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero, map_zero]
      have k := hg U s t₁ (e.symm.toRingHom.comp (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I)))
        (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [a₁]; simp)
      apply e.symm.injective
      rw [map_one]
      exact k.symm.trans (h₁ U hU _ _)
  have k := hg W (𝟙 W) t (AddMonoidAlgebra.liftNCRingHom (RingHom.id _)
    ((Units.coeHom _).comp (splitTorusPointsEquiv _ X W t)) fun _ _ => Commute.all _ _)
    (fun b => by simp) (fun χ => by simp [chV])
  rwa [Category.id_comp, one, map_one] at k

theorem unit_eq_one : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') y).left z ⊤ u = gm (lift t y).left z ⊤ u * gm (lift t' y).left z ⊤ u) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ u = 1) → u = 1 := by
  intro A _ J hJ X _ Y u hm h₁
  have hm' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u.val =
        (lift t y).left.appTop.hom u.val * (lift t' y).left.appTop.hom u.val := fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom u =
        Units.map (lift t y).left.appTop.hom.toMonoidHom u * Units.map (lift t' y).left.appTop.hom.toMonoidHom u :=
      unit_ext fun z _ => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, hm]
    exact congrArg Units.val e
  have h₁' : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), (lift t y).left.appTop.hom u.val = 1 := fun Z hZ t y => by
    have e : Units.map (lift t y).left.appTop.hom.toMonoidHom u = 1 :=
      unit_ext fun z _ => by rw [map_one, ← gm_top, h₁ Z hZ]
    exact congrArg Units.val e
  refine unit_ext fun z _ => ?_
  let 𝒰 := (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left.affineCover
  obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq z
  let W : Over (Spec (CommRingCat.of A)) := Over.mk (𝒰.f i ≫ (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).hom)
  haveI : IsAffine W.left := inferInstanceAs (IsAffine (𝒰.X i))
  let κ : W ⟶ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y := Over.homMk (𝒰.f i) rfl
  have e := eq_one_affine J hJ u.val hm' h₁' (κ ≫ fst _ _) (κ ≫ snd _ _)
  rw [lift_comp_fst_snd] at e
  have e' : Units.map (𝒰.f i).appTop.hom.toMonoidHom u = 1 := Units.ext e
  refine gm_inj (U := ⊤) (U' := ⊤) (𝒰.f i) w trivial trivial ?_
  rw [gm_top, e', map_one, map_one]

end GlobalTheory.UU.UnitRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_gen_mulPull_pow_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (n k k' : ℕ), k' = k * n ^ 2 → ∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, (𝟙 G ^ n).left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen := by
  intro R _ _ I D A G _ _ U n k k' hk
  have hL := U.LG.isLB
  have hcube : GlobalTheory.MulPull.HasGen U.LG.L (thφ G (x3 G)) thε := ⟨U.cubG.t, U.cubG.isGen⟩
  have hrig : GlobalTheory.MulPull.HasGen U.LG.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) :=
    ⟨U.LG.rig, U.LG.rigGen⟩
  have hneg : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] :=
    ⟨U.symG, U.symG_gen⟩
  have main : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      ![(n : ℤ) ^ 2, -1] := by
    refine GlobalTheory.MulPull.hasGen_pow hL hcube (𝟙 G) ?_ ?_ n
    · refine (hrig.pull (toUnit G).left).of_formEq hL (fun W _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine hneg.inv.of_formEq hL (fun W _ h => ?_)
      have e : ((𝟙 G : G ⟶ G)⁻¹) = ι[G] := Category.id_comp _
      rw [e]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        _root_.mul_one, neg_neg]
      exact _root_.mul_comm _ _
  obtain ⟨t, ht⟩ := main
  have hp : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      (fun i => (k : ℤ) * (![(n : ℤ) ^ 2, -1] : Fin 2 → ℤ) i) := ⟨_, powGen_isGen _ _ _ t ht k⟩
  refine hp.of_formEq hL (fun W _ h => ?_)
  subst hk
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    _root_.mul_one, mul_neg]
  push_cast
  rfl

end GlobalTheory.UT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.NonVan
open GlobalTheory.UT.CoefBasic

theorem val_powFrame {S : Scheme.{0}} {A : Over S} (L : LB A.left) {T : Over S} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame A L x τ k) r z J = val τ r z J ^ k :=
  map_zpow _ _ _

theorem exists_sec_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 4 ≤ k → ∀ (x : TFK (R := R) F ⟶ A.A) (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), e.IsGen → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) := by
  intro hL R _ _ A F _ _ k hk x e he
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  obtain ⟨t, ht⟩ := GlobalTheory.TwistUnit.unitAt_pow hL.1.ample A k hk (snd (TFK (R := R) F) A.A).left
    ((ptSecT A.A x).left z)
  have hu := GlobalTheory.TwistUnit.isUnit_sval_of A.isLB t (ptSecT A.A x).left z ht J' hJ'
  obtain ⟨c, hc⟩ := cstH_surj z (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val
  refine ⟨t, c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq (R := R) z z'
    have a₁ := sval_tr t (ptSecT A.A x).left hJ hJ'
    have a₂ := val_tr he (𝟙 _) hJ hJ'
    have hx : (ptSecT A.A x).left ≫ (snd (TFK (R := R) F) A.A).left = x.left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [Fin.prod_univ_one, hx, ← hu.unit_spec] at a₁
    rw [Fin.prod_univ_one, Category.id_comp, zpow_one] at a₂
    have a₃ : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) =
        (hu.unit * (val e (𝟙 _) z J' ^ (k : ℤ))⁻¹).val := (cst_eq z c).trans hc
    refine a₁.trans ?_
    rw [a₃, val_powFrame, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module

end GlobalTheory.UT.NonVan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQkStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.torsionPoint_qk_alt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.b ^ k = 1 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ p : QkPt D.toPre F k, p.y = 0 ∧ GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g := by
  first | exact @GlobalTheory.TorsionQk.torsionPoint_qk | exact GlobalTheory.TorsionQk.torsionPoint_qk | (intros; apply GlobalTheory.TorsionQk.torsionPoint_qk <;> assumption)
end

