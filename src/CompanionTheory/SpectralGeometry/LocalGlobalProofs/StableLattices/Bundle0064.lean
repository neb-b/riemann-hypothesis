module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsIsoOfClosedImmersion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualUniv

theorem isIso_of_closedImmersion {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Sp R) [IsClosedImmersion f]
    [Flat f] [Surjective f] : IsIso f := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have h₁ : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).1 ⟨inferInstance, inferInstance⟩
  have h₂ : Function.Surjective f.appTop.hom := (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  have h₃ : Function.Bijective f.appTop.hom := ⟨h₁.injective, h₂⟩
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2 h₃
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine f)).2
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

variable {S : Scheme.{0}}

def IsAddCls (A : Over S) [GrpObj A] (m : Pic A.left) : Prop :=
  ∀ (Y : Over S) (a a' : Y ⟶ A),
    CechPic.pull (a * a').left m = CechPic.pull a.left m + CechPic.pull a'.left m

theorem preDual_baseChange {S' : Scheme.{0}} {b : S' ⟶ S} {A B : Over S} [GrpObj A] [GrpObj B] {A' B' : Over S'}
    [GrpObj A'] [GrpObj B'] {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP' : P'.IsLB) (e : LBIso (P.pull h) P')
    (hd : PreDual A B P) : PreDual A' B' P' := by
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_pull hf hg h₁ h₂ hd.isLB hP' e hd.add₁ hd.add₂
  refine ⟨hP', a₁, a₂, fun T y hy ↦ ?_, fun k _ _ t ↦ ?_⟩
  · have h0 := hd.right _ (pushP hg (s := T.hom) rfl y) ((triv_ev_iff hd.isLB _ _).2 (by
      rw [← evc_trR hf hg h₁ h₂ hd.isLB hP' e, (triv_ev_iff hP' _ _).1 hy, map_zero]))
    exact pt_ext hg ((congrArg (fun z ↦ z.left) h0).trans (one_left_comp hg (s := T.hom) rfl).symm)
  · refine Set.Finite.of_injOn (f := pushP hf (s := t) rfl) (fun x hx ↦ ?_)
      (fun x _ y _ e ↦ pt_ext hf (congrArg (fun z ↦ z.left) e)) (hd.left k (t ≫ b))
    refine (triv_ev_iff hd.isLB _ _).2 ?_
    have := evc_trL hf hg h₁ h₂ hd.isLB hP' e (Over.mk t) x
    rw [(triv_ev_iff hP' _ _).1 hx, map_zero] at this
    exact this.symm

theorem exists_point_fibre (H3 : PointSurj) {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hP : PreDual A B P) {m : Pic A.left} (hm : IsAddCls A m)
    (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ S) :
    ∃ y : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s) ⟶ B,
      evc hP.isLB (fst A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s)))
          (snd A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s)) ≫ y) =
        CechPic.pull (fst A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s))).left m := by
  have hf := isGrpPullback_pullback A s
  have hg := isGrpPullback_pullback B s
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hf hg
  have hP' : (P.pull h).IsLB := pull_isLB hP.isLB h
  have e : LBIso (P.pull h) (P.pull h) := (cls_eq_iff hP' hP').1 rfl
  have hd := preDual_baseChange hf hg h₁ h₂ hP' e hP
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hf
  have hB' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hg
  obtain ⟨M, hM, eM⟩ := cls_surj (CechPic.pull
    ((fst ((Over.pullback s).obj A) (𝟙_ (Over (Sp k)))).left ≫ pullback.fst A.hom s) m)
  have hadd : IsAdditive M := (isAdditive_iff hM).2 fun Y a a' t ↦ by
    simp only [evc, eM, ← pull_comp, lift_left_fst_assoc]
    rw [mul_left_comp hf (s₀ := Y.hom ≫ s) rfl (x := a) (y := a') (x₀ := pushP hf (s := Y.hom) rfl a)
      (y₀ := pushP hf (s := Y.hom) rfl a') rfl rfl]
    exact hm _ _ _
  have fin : Set.Finite {x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback s).obj A |
      Triv (ev (P.pull h) (toUnit ((Over.pullback s).obj B) ≫ x) (𝟙 ((Over.pullback s).obj B)))} := by
    refine (hd.left k (𝟙 _)).subset fun x hx ↦ ?_
    refine (triv_ev_iff hP' _ _).2 ?_
    have e₂ := congrArg (CechPic.pull (snd (𝟙_ (Over (Sp k))) ((Over.pullback s).obj B)).left)
      ((triv_ev_iff hP' _ _).1 hx)
    rw [pull_evc, map_zero, Category.comp_id, ← Category.assoc,
      toUnit_unique (snd (𝟙_ (Over (Sp k))) ((Over.pullback s).obj B) ≫ toUnit _) (fst _ _)] at e₂
    exact e₂
  obtain ⟨y, hy⟩ := H3 k _ _ hA' hB' (P.pull h) hP' hd.add₁ hd.add₂ fin M hM hadd
  refine ⟨pushP hg (s := (𝟙_ (Over (Sp k))).hom) rfl y, ?_⟩
  have c := (cls_eq_iff hM (pull_isLB hP' _)).2 hy
  rw [← evc_trR hf hg h₁ h₂ hP.isLB hP' e]
  have c' : evc hP' (fst _ _) (snd _ _ ≫ y) = _ := c.symm.trans eM
  rw [c', ← pull_comp]
  exact congrArg (fun q ↦ CechPic.pull q m) (trR_fst hf _)

theorem exists_section (H1 : TrivLocus) (H2 : TrivLocusFlat) (H3 : PointSurj) {C : Type} [CommRing C]
    [IsNoetherianRing C] (A B : Over (Sp C)) [GrpObj A] [GrpObj B] (g : ℕ) (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) (gA : SmoothOfRelativeDimension g A.hom) (gB : SmoothOfRelativeDimension g B.hom)
    {P : LB (A ⊗ B).left} (hP : PreDual A B P) {m : Pic A.left} (hm : IsAddCls A m) :
    ∃ x : Over.mk (𝟙 (Sp C)) ⟶ B, evc hP.isLB (fst A (Over.mk (𝟙 (Sp C)))) (snd A (Over.mk (𝟙 (Sp C))) ≫ x) =
      CechPic.pull (fst A (Over.mk (𝟙 (Sp C)))).left m := by
  obtain ⟨N, hN, eN⟩ := cls_surj (cls P hP.isLB - CechPic.pull (fst A B).left m)
  have ecl : ∀ {Y : Over (Sp C)} (a : Y ⟶ A) (t : Y ⟶ B),
      evc hN a t = evc hP.isLB a t - CechPic.pull a.left m := by
    intro Y a t
    rw [evc, eN, map_sub, ← pull_comp, lift_left_fst]
    rfl
  have rep : ∀ (T : Over (Sp C)) (y : T ⟶ B), Triv (ev N (fst A T) (snd A T ≫ y)) ↔
      evc hP.isLB (fst A T) (snd A T ≫ y) = CechPic.pull (fst A T).left m := fun T y ↦ by
    rw [triv_ev_iff hN, ecl, sub_eq_zero]
  have h0 : Triv (ev N (1 : B ⟶ A) (𝟙 B)) := by
    have z : CechPic.pull (1 : B ⟶ A).left m = 0 := by
      have := hm B 1 1
      rw [_root_.mul_one] at this
      exact left_eq_add.1 this
    rw [triv_ev_iff hN, ecl, hP.add₁.evc_one hP.isLB, z, sub_zero]
  have tr := GlobalTheory.BirigidLift.triv_right hP.isLB hP.add₂
  have uniq : ∀ (T : Over (Sp C)) (y y' : T ⟶ B),
      evc hP.isLB (fst A T) (snd A T ≫ y) = CechPic.pull (fst A T).left m →
      evc hP.isLB (fst A T) (snd A T ≫ y') = CechPic.pull (fst A T).left m → y = y' := by
    intro T y y' e e'
    have a2 := (GlobalTheory.BirigidLift.isAdditive_swap_iff hP.isLB).1 hP.add₂
    have k1 := a2 _ (fst A T) (snd A T ≫ y) (snd A T ≫ y'⁻¹)
    have k2 := a2 _ (fst A T) (snd A T ≫ y') (snd A T ≫ y'⁻¹)
    rw [← MonObj.comp_mul] at k1 k2
    rw [_root_.mul_inv_cancel, MonObj.comp_one, evc_one_right hP.isLB tr] at k2
    have z := hP.right T (y * y'⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by rw [k1, e, ← e', ← k2]))
    exact mul_inv_eq_one.1 z
  have : LocallyOfFiniteType B.hom := by
    have := hB.smooth
    infer_instance
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  obtain ⟨Z, i, hci, hiff⟩ := H1 _ A B hA ‹_› N hN h0
  have : IsClosedImmersion i.left := hci
  have hw : i.left ≫ B.hom = Z.hom := Over.w i
  have hmono : Mono Z.hom := ⟨fun {W} u v e ↦ by
    let u' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk u rfl
    let v' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk v e.symm
    have e₁ := uniq _ (u' ≫ i) (v' ≫ i) ((rep _ _).1 ((hiff _ _).2 ⟨u', rfl⟩))
      ((rep _ _).1 ((hiff _ _).2 ⟨v', rfl⟩))
    exact (cancel_mono i.left).1 (congrArg (fun q ↦ q.left) e₁)⟩
  have hprop : IsProper Z.hom := by
    have := hB.proper
    rw [← hw]
    infer_instance
  have hcl : IsClosedImmersion Z.hom := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hprop, hmono⟩
  have hfl : Flat Z.hom := H2 _ A B Z g hA gA gB N hN i ⟨hci, hiff⟩ inferInstance
  have hsu : Surjective Z.hom := ⟨fun c ↦ by
    let κ := (Sp C).residueField c
    let k := AlgebraicClosure κ
    let s : Sp k ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ (Sp C).fromSpecResidueField c
    obtain ⟨y, hy⟩ := exists_point_fibre H3 hA hB hP hm k s
    obtain ⟨z, rfl⟩ := (hiff _ y).1 ((rep _ _).2 hy)
    obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
    refine ⟨z.left p, ?_⟩
    have e : z.left ≫ Z.hom = (𝟙_ (Over (Sp k))).hom ≫ s := Over.w z
    have e' : z.left ≫ Z.hom = s := e.trans (Category.id_comp s)
    rw [← Scheme.Hom.comp_apply, e']
    exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply c _)⟩
  have : IsIso Z.hom := isIso_of_closedImmersion Z.hom
  let z : Over.mk (𝟙 (Sp C)) ⟶ Z := Over.homMk (inv Z.hom) (by simp)
  exact ⟨z ≫ i, (rep _ _).1 ((hiff _ _).2 ⟨z, rfl⟩)⟩

theorem univNoeth : TrivLocus → TrivLocusFlat → PointSurj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, PreDual A B P → UnivNoeth A B P := by
  intro H1 H2 H3 R _ _ A B _ _ g hA hB gA gB P hP C _ _ t M hM hadd
  have hf := isGrpPullback_pullback A t
  have hg := isGrpPullback_pullback B t
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hf hg
  have hP' : (P.pull h).IsLB := pull_isLB hP.isLB h
  have e : LBIso (P.pull h) (P.pull h) := (cls_eq_iff hP' hP').1 rfl
  have hd := preDual_baseChange hf hg h₁ h₂ hP' e hP
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hf
  have hB' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hg
  have gA' : SmoothOfRelativeDimension g ((Over.pullback t).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hf.1 gA
  have gB' : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hg.1 gB
  let r : ((Over.pullback t).obj A).left ⟶ (A ⊗ Over.mk t).left :=
    Limits.pullback.lift (pullback.fst A.hom t) ((Over.pullback t).obj A).hom hf.1.w
  have r₁ : r ≫ (fst A (Over.mk t)).left = pullback.fst A.hom t := Limits.pullback.lift_fst _ _ _
  have r₂ : r ≫ (snd A (Over.mk t)).left = ((Over.pullback t).obj A).hom := Limits.pullback.lift_snd _ _ _
  have key : ∀ (Y : Over (Sp C)) (a : Y ⟶ (Over.pullback t).obj A) (a₀ : Over.mk (Y.hom ≫ t) ⟶ A),
      a.left ≫ pullback.fst A.hom t = a₀.left →
      CechPic.pull a.left (CechPic.pull r (cls M hM)) =
        evc hM a₀ (Over.homMk Y.hom rfl : Over.mk (Y.hom ≫ t) ⟶ Over.mk t) := by
    intro Y a a₀ ea
    rw [← pull_comp, evc]
    refine congrArg (fun q ↦ CechPic.pull q (cls M hM)) (left_ext ?_ ?_)
    · rw [Category.assoc, r₁, lift_left_fst, ea]
    · rw [Category.assoc, r₂, lift_left_snd]
      exact Over.w a
  have hm : IsAddCls ((Over.pullback t).obj A) (CechPic.pull r (cls M hM)) := fun Y a a' ↦ by
    rw [key Y (a * a') (pushP hf (s := Y.hom) rfl a * pushP hf (s := Y.hom) rfl a')
        (mul_left_comp hf rfl rfl rfl), key Y a (pushP hf (s := Y.hom) rfl a) rfl,
      key Y a' (pushP hf (s := Y.hom) rfl a') rfl]
    exact (isAdditive_iff hM).1 hadd _ _ _ _
  obtain ⟨x', hx⟩ := exists_section H1 H2 H3 _ _ g hA' hB' gA' gB' hd hm
  have wx : x'.left ≫ ((Over.pullback t).obj B).hom = 𝟙 (Sp C) := Over.w x'
  let x : Over.mk t ⟶ B := Over.homMk (x'.left ≫ pullback.fst B.hom t) (by
    show (x'.left ≫ pullback.fst B.hom t) ≫ B.hom = t
    rw [Category.assoc, hg.1.w, ← Category.assoc, wx]
    exact Category.id_comp t)
  refine ⟨x, (cls_eq_iff hM (pull_isLB hP.isLB _)).1 ?_⟩
  have w : (fst A (Over.mk t)).left ≫ A.hom = (snd A (Over.mk t)).left ≫ t :=
    (Over.w (fst A (Over.mk t))).trans (Over.w (snd A (Over.mk t))).symm
  let a := liftPt hf (snd A (Over.mk t)).left (fst A (Over.mk t)).left w
  let τ : Over.mk (snd A (Over.mk t)).left ⟶ Over.mk (𝟙 (Sp C)) :=
    Over.homMk (snd A (Over.mk t)).left (by simp)
  have ar : a.left ≫ r = 𝟙 _ := by
    apply left_ext
    · rw [Category.assoc, r₁, Category.id_comp]
      exact liftPt_left _ _ _ _
    · rw [Category.assoc, r₂, Category.id_comp]
      exact Over.w a
  have c := congrArg (CechPic.pull (lift a τ).left) hx
  rw [pull_evc, ← pull_comp, lift_left_fst, lift_fst, lift_snd_assoc,
    evc_eq h₁ h₂ hP.isLB hP' e a (τ ≫ x') (fst A (Over.mk t)) (snd A (Over.mk t) ≫ x)
      (liftPt_left _ _ _ _) rfl, ← pull_comp, ar] at c
  exact (c.trans (pull_id _)).symm

end GlobalTheory.CompanionTheory.DualUniv
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialAfterFlatCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigCover

theorem exists_gen_of_chart {Y P : Scheme.{0}} {M : LB P} (hM : M.IsLB) (f : Y ⟶ P) (i : M.ι)
    (hf : ∀ y, f y ∈ M.U i) : ∃ t : LB.Gen (M.pull f), t.IsGen := by
  have le (J : (M.pull f).ι) : (M.pull f).U J ≤ f ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U i) :=
    fun y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => Units.map (f.appLE _ _ (le J)).hom.toMonoidHom (M.g (J PUnit.unit) i)⟩, ?_⟩
  intro J J'
  let j := J PUnit.unit
  let k := J' PUnit.unit
  let U := (M.pull f).U J ⊓ (M.pull f).U J'
  let V := M.U j ⊓ M.U k ⊓ M.U i
  have hUV : U ≤ f ⁻¹ᵁ V := fun y hy => ⟨⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩, hf y⟩
  let pullToU := Units.map (f.appLE V U hUV).hom.toMonoidHom
  have pull_res {A : P.Opens} (h : V ≤ A) (a : Γ(P, A)ˣ) :
      pullToU (res h a) = Units.map (f.appLE A U (hUV.trans (f.preimage_mono h))).hom.toMonoidHom a := by
    apply Units.ext
    exact congrArg (fun q => q.hom a.val) (f.map_appLE hUV (homOfLE h).op)
  have res_pull {A : P.Opens} {B : Y.Opens} (h : B ≤ f ⁻¹ᵁ A) (h' : U ≤ B) (a : Γ(P, A)ˣ) :
      res h' (Units.map (f.appLE A B h).hom.toMonoidHom a) = Units.map (f.appLE A U (h'.trans h)).hom.toMonoidHom a := by
    apply Units.ext
    exact congrArg (fun q => q.hom a.val) (f.appLE_map h (homOfLE h').op)
  have transition : (M.pull f).g J J' = pullToU (res inf_le_left (M.g j k)) := by
    show (∏ _ : PUnit, (res _ (pullU f _ (M.g j k))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one, pull_res]
    rfl
  change res (_ : U ≤ (M.pull f).U J) (Units.map (f.appLE _ _ (le J)).hom.toMonoidHom (M.g j i)) =
    (M.pull f).g J J' * res (_ : U ≤ (M.pull f).U J') (Units.map (f.appLE _ _ (le J')).hom.toMonoidHom (M.g k i))
  calc
    _ = pullToU (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (M.g j i)) :=
      (res_pull (le J) inf_le_left _).trans (pull_res _ _).symm
    _ = pullToU (res inf_le_left (M.g j k)) *
        pullToU (res (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g k i)) := by
      rw [← map_mul]
      exact congrArg pullToU (hM.cocycle j k i).symm
    _ = _ := congrArg₂ (· * ·) transition.symm
      ((pull_res _ _).trans (res_pull (le J') inf_le_right _).symm)

theorem exists_flat_cover_triv : ∀ {P : Scheme.{0}} (M : LB P), M.IsLB → ∃ (Z : Scheme.{0}) (g : Z ⟶ P),
    Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧ Triv (M.pull g) := by
  intro P M hM
  let D : M.ι → Scheme.{0} := fun i => (M.U i).toScheme
  let g : ∐ D ⟶ P := Sigma.desc fun i => (M.U i).ι
  have hι : ∀ i, Sigma.ι D i ≫ g = (M.U i).ι := fun i => Sigma.ι_comp_desc _ i
  refine ⟨∐ D, g, ?_, ?_, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    have hf : ∀ i : M.ι, Flat (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @Flat) (sigmaOpenCover D) hf
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    have hf : ∀ i : M.ι, LocallyOfFinitePresentation (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover D) hf
  · refine ⟨fun x => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart hM x
    let x' : D i := ⟨x, hi⟩
    refine ⟨Sigma.ι D i x', ?_⟩
    have e : (Sigma.ι D i ≫ g) x' = x := by rw [hι]; rfl
    exact e
  · let Z := ∐ D
    let σ (s : M.ι) : D s ⟶ Z := Sigma.ι D s
    have cover (y : Z) : ∃ s, y ∈ (σ s).opensRange := by
      obtain ⟨s, x, rfl⟩ := (sigmaOpenCover D).exists_eq y
      exact ⟨s, x, rfl⟩
    have sections (U : Z.Opens) (V : ∀ s, (D s).Opens) (hV : ∀ s, V s = σ s ⁻¹ᵁ U) :
        Function.Bijective (fun a : Γ(Z, U)ˣ => fun s =>
          Units.map ((σ s).appLE U (V s) (hV s).le).hom.toMonoidHom a) := by
      have hv : V = fun s => σ s ⁻¹ᵁ U := funext hV
      subst V
      simp only [Scheme.Hom.appLE_eq_app]
      let E (s : M.ι) := (σ s).opensRange ⊓ U
      let e (s : M.ι) := IsOpenImmersion.ΓIso (σ s) U
      have hc : U ≤ ⨆ s, E s := fun y hy => by
        obtain ⟨s, hs⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨s, hs, hy⟩
      have restrict (a : Γ(Z, U)) (s : M.ι) :
          (e s).hom.hom (((σ s).app U).hom a) =
            (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom a :=
        congrArg (fun q => q.hom a) (IsOpenImmersion.app_ΓIso_hom (σ s) U)
      have compatible (a : ∀ s, Γ(Z, E s)) : TopCat.Presheaf.IsCompatible Z.sheaf.1 E a := by
        intro s s'
        by_cases he : s = s'
        · subst s'
          rfl
        · apply TopCat.Presheaf.section_ext Z.sheaf (E s ⊓ E s')
          intro y hy
          have hd := disjoint_iff.1 (disjoint_opensRange_sigmaι D s s' he)
          have hm : y ∈ (σ s).opensRange ⊓ (σ s').opensRange := ⟨hy.1.1, hy.2.1⟩
          rw [hd] at hm
          exact hm.elim
      have ext_sections (a b : Γ(Z, U))
          (h : ∀ s, (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom a =
            (Z.presheaf.map (homOfLE (inf_le_right : E s ≤ U)).op).hom b) : a = b :=
        Z.sheaf.eq_of_locally_eq' E U (fun _ => homOfLE inf_le_right) hc a b h
      constructor
      · intro a b hab
        apply Units.ext
        apply ext_sections
        intro s
        rw [← restrict, ← restrict]
        exact congrArg (fun u : Γ(D s, σ s ⁻¹ᵁ U)ˣ => (e s).hom.hom u.val)
          (congrFun hab s)
      · intro a
        let b (s : M.ι) : Γ(Z, E s)ˣ := Units.map (e s).hom.hom.toMonoidHom (a s)
        obtain ⟨u, hu, _⟩ := Z.sheaf.existsUnique_gluing' E U (fun _ => homOfLE inf_le_right) hc
          (fun s => (b s).val) (compatible _)
        obtain ⟨v, hv, _⟩ := Z.sheaf.existsUnique_gluing' E U (fun _ => homOfLE inf_le_right) hc
          (fun s => (b s).inv) (compatible _)
        have huv : u * v = 1 := by
          apply ext_sections
          intro s
          simp only [map_mul, map_one]
          exact (congrArg₂ (· * ·) (hu s) (hv s)).trans (b s).val_inv
        refine ⟨⟨u, v, huv, (mul_comm v u).trans huv⟩, funext fun s => ?_⟩
        apply Units.ext
        apply (e s).commRingCatIsoToRingEquiv.injective
        exact (restrict u s).trans (hu s)
    let L := M.pull g
    let Ls (s : M.ι) := M.pull (σ s ≫ g)
    have localGen (s : M.ι) : ∃ t : LB.Gen (Ls s), t.IsGen := by
      refine exists_gen_of_chart hM (σ s ≫ g) s fun y => ?_
      change (Sigma.ι D s ≫ g) y ∈ M.U s
      rw [hι]
      exact y.2
    choose t ht using localGen
    have charts (s : M.ι) (J : L.ι) : (Ls s).U J = σ s ⁻¹ᵁ L.U J := by
      ext y
      exact mem_pull.trans (mem_pull (F := g)).symm
    let pullOn (s : M.ι) (A : Z.Opens) (B : (D s).Opens) (h : B ≤ σ s ⁻¹ᵁ A) :=
      Units.map ((σ s).appLE A B h).hom.toMonoidHom
    have glue (J : L.ι) : ∃ a : Γ(Z, L.U J)ˣ,
        ∀ s, pullOn s _ _ (charts s J).le a = (t s).s J := by
      obtain ⟨a, ha⟩ := (sections (L.U J) (fun s => (Ls s).U J) (fun s => charts s J)).2
        (fun s => (t s).s J)
      exact ⟨a, fun s => congrFun ha s⟩
    choose a ha using glue
    refine ⟨⟨a⟩, ?_⟩
    intro J J'
    let U := L.U J ⊓ L.U J'
    let V (s : M.ι) := (Ls s).U J ⊓ (Ls s).U J'
    have hV (s : M.ι) : V s = σ s ⁻¹ᵁ U := by
      change (Ls s).U J ⊓ (Ls s).U J' = _
      rw [charts, charts]
      rfl
    apply (sections U V hV).1
    funext s
    change pullOn s U (V s) (hV s).le (res inf_le_left (a J)) =
      pullOn s U (V s) (hV s).le (L.g J J' * res inf_le_right (a J'))
    have pull_restrict {A : Z.Opens} {B : (D s).Opens} (h : U ≤ A) (h' : V s ≤ B)
        (hB : B ≤ σ s ⁻¹ᵁ A) (b : Γ(Z, A)ˣ) :
        pullOn s U (V s) (hV s).le (res h b) = res h' (pullOn s A B hB b) := by
      apply Units.ext
      exact congrArg (fun q => q.hom b.val)
        (((σ s).map_appLE (hV s).le (homOfLE h).op).trans
          ((σ s).appLE_map hB (homOfLE h').op).symm)
    have transitions : pullOn s U (V s) (hV s).le (L.g J J') = (Ls s).g J J' := by
      let j := J PUnit.unit
      let k := J' PUnit.unit
      show pullOn s U (V s) (hV s).le
          (∏ _ : PUnit, res _ (pullU g _ (M.g j k)) ^ (1 : ℤ)) =
        ∏ _ : PUnit, res _ (pullU (σ s ≫ g) _ (M.g j k)) ^ (1 : ℤ)
      simp only [Fintype.prod_unique, zpow_one]
      apply Units.ext
      exact congrArg (fun q => q.hom (M.g j k).val)
        (Scheme.Hom.appLE_comp_appLE (σ s) g _ U (V s) _ (hV s).le)
    rw [map_mul, pull_restrict inf_le_left inf_le_left (charts s J).le,
      pull_restrict inf_le_right inf_le_right (charts s J').le, ha, ha, transitions]
    exact ht s J J'

end GlobalTheory.CompanionTheory.RigCover
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivial
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PicField

theorem pic_eq_zero (k : Type) [Field k] (c : Pic (Sp k)) : c = 0 := by
  obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c p
  have hV' : V = ⊤ := by
    have hs : Subsingleton (Sp k) := by
      unfold Sp; infer_instance
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (Subsingleton.elim x p) ▸ hV
  subst hV'
  have : IsIso (⊤ : (Sp k).Opens).ι := (Sp k).topIso.isIso_hom
  have e : c = CechPic.pull (inv (⊤ : (Sp k).Opens).ι) (CechPic.pull (⊤ : (Sp k).Opens).ι c) := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [e, hc, map_zero]

end GlobalTheory.CompanionTheory.PicField
end
end

