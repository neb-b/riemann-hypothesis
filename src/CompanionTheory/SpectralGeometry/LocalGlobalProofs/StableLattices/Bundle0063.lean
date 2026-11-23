module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonOfForallIsMaximalSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem fibAc_of_closed_fibres : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  intro k _ _ X T Z a b p q H ha _ _ G hG R _ t _ Y π f Hy hfib κ _ _ D hD hc n
  have HP := Hy.paste_horiz H
  have hproj : IsProjBy f := by
    obtain ⟨c, hcb⟩ := Spec.map_surjective (t ≫ b)
    have HP' : IsPullback (π ≫ p) f a (spMap c.hom) := by
      have : spMap c.hom = t ≫ b := by
        rw [← hcb]; rfl
      rw [this]; exact HP
    exact (ProjSpace.isProjBy_iff_isProjOver f).2
      (ProjSpace.isProjOver_of_isPullback_spMap c.hom HP'
        ((ProjSpace.isProjBy_iff_isProjOver a).1 ha))
  haveI : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) HP inferInstance
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) HP inferInstance
  haveI hN : IsNoetherianRing R := by
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
      LocallyOfFiniteType.isLocallyNoetherian (t ≫ b)
    exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).1 inferInstance
  have hM := LB.isLB_pull hG π
  have hI := GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated f hD
  have hflat : ∀ p, Module.Flat R ((cechLB f (G.pull π) D).X p) := flat_cechLB_X f hM hI
  have hfin := _root_.GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover R Y f _ κ D hM inferInstance hproj hD hc
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine GlobalTheory.MumfordAway.subsingleton_of_points k R (t ≫ b) _ fun χ hχ => ?_
  refine exists_smul_homology_eq_zero_of_acyclic_fibre R k χ _ (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) hflat hfin ?_ n
  have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  have P1 := h'.paste_horiz HP
  rw [hχ] at P1
  let u := pullback.fst f (Spec.map (CommRingCat.ofHom χ))
  let v := pullback.snd f (Spec.map (CommRingCat.ofHom χ))
  let e := u ≫ π ≫ p
  haveI : IsIso e := P1.isIso_fst_of_isIso
  have he : e ≫ a = v := P1.w.trans (Category.comp_id _)
  let σ : X ⟶ Z := inv e ≫ u ≫ π
  have hσp : σ ≫ p = 𝟙 X := by
    simp only [σ, Category.assoc]
    exact IsIso.inv_hom_id e
  have hes : e ≫ σ = u ≫ π := by simp [σ]
  have hσq : σ ≫ q = a ≫ Spec.map (CommRingCat.ofHom χ) ≫ t := by
    rw [← cancel_epi e, ← Category.assoc e σ, hes, ← Category.assoc e a, he, Category.assoc u, Hy.w]
    exact (reassoc_of% h'.w) t
  have hac := hfib (Spec.map (CommRingCat.ofHom χ)) σ hχ hσp hσq κ (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i)
    (fun i => (isAffineOpen_preimage_of_isPullback h' (hD i)).preimage_of_isIso _)
    (by rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hc]; rfl)
  obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion k X a (G.pull σ) _ e κ
    (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i) (LB.isLB_pull hG σ)
    (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  have hD' : (fun i => e ⁻¹ᵁ inv e ⁻¹ᵁ u ⁻¹ᵁ D i) = fun i => u ⁻¹ᵁ D i := funext fun i => by
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]; rfl
  rw [he, hD'] at i₁
  obtain ⟨w₁, hw₁⟩ : ∃ w : LB.Iso ((G.pull σ).pull e) (G.pull (u ≫ π)), w.IsGen :=
    hes ▸ GlobalTheory.MumfordSupport.exists_iso_pull_pull hG σ e
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.MumfordSupport.exists_iso_pull_pull hG π u
  have hL₁ : ((G.pull σ).pull e).IsLB := LB.isLB_pull (LB.isLB_pull hG σ) e
  have hL₂ : ((G.pull π).pull u).IsLB := LB.isLB_pull hM u
  have hL₃ : (G.pull (u ≫ π)).IsLB := LB.isLB_pull hG _
  have c₁ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₁ hL₃ w₁ hw₁
  have c₂ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₂ hL₃ w₂ hw₂
  have E := cechLBBaseChangeIso hM h' hI ≪≫ c₂ ≪≫ c₁.symm ≪≫ i₁
  exact fun m => (hac m).of_iso E.symm

end GlobalTheory.CompanionTheory.PointSurjectivity
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteGroupHomKernelPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.KerPull.Kernel

section General

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A A' H : C} [GrpObj A] [GrpObj A']
  {q : A ⟶ A'} [IsMonHom q] {i : H ⟶ A}

theorem mono_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) : Mono i :=
  ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩

def kerLift (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) : W ⟶ H :=
  hp.lift f (toUnit W) (by rw [hf, Hom.one_def])

theorem kerLift_comp (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) :
    kerLift hp f hf ≫ i = f :=
  hp.lift_fst ..

theorem comp_kills (hp : IsPullback i (toUnit H) q η[A']) {W : C} (x : W ⟶ H) : (x ≫ i) ≫ q = 1 := by
  rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]

@[instance_reducible]
def grpObjOfIsKernel (hp : IsPullback i (toUnit H) q η[A']) : GrpObj H :=
  have := mono_of_isKernel hp
  { one := kerLift hp η[A] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    mul := kerLift hp (fst H H ≫ i * snd H H ≫ i) (by
      rw [MonObj.mul_comp, comp_kills hp, comp_kills hp, _root_.mul_one])
    inv := kerLift hp (i ≫ ι[A]) (by
      have e : i ≫ q = 1 := by simpa using comp_kills hp (𝟙 H)
      have h : (i⁻¹ * i) ≫ q = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
      rw [MonObj.mul_comp, e, _root_.mul_one] at h
      exact h)
    one_mul := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (fst (𝟙_ C) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (snd H (𝟙_ C)) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      exact _root_.mul_assoc _ _ _
    left_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact inv_mul_cancel i
    right_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact mul_inv_cancel i }

theorem isMonHom_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsMonHom i := by
  letI := grpObjOfIsKernel hp
  refine { one_hom := kerLift_comp hp _ _, mul_hom := ?_ }
  refine (kerLift_comp hp _ _).trans ?_
  rw [Hom.mul_def]
  simp

theorem isCommMonObj_of_isKernel [BraidedCategory C] [IsCommMonObj A]
    (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsCommMonObj H := by
  letI := grpObjOfIsKernel hp
  have := mono_of_isKernel hp
  have := isMonHom_of_isKernel hp
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
  rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end General

theorem exists_finite_kernel : ∀ (k : Type) [Field k] (A A' : Over (Sp k)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → ∀ (q : A ⟶ A'), IsMonHom q → IsFinite q.left →
    ∃ (H : Over (Sp k)) (_ : GrpObj H) (_ : IsCommMonObj H) (i : H ⟶ A), IsMonHom i ∧ IsFinite H.hom ∧
      IsPullback i (toUnit _) q η[A'] := by
  intro k _ A A' _ _ hA q hq hf
  have := hA.comm
  have hp : IsPullback (pullback.fst q η[A']) (toUnit (pullback q η[A'])) q η[A'] := by
    rw [toUnit_unique (toUnit _) (pullback.snd q η[A'])]
    exact IsPullback.of_hasPullback _ _
  refine ⟨pullback q η[A'], grpObjOfIsKernel hp, isCommMonObj_of_isKernel hp, pullback.fst _ _,
    isMonHom_of_isKernel hp, ?_, hp⟩
  have hl := hp.map (Over.forget _)
  have h1 : IsFinite (toUnit (pullback q η[A'])).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hl hf
  have h2 : (pullback q η[A']).hom = (toUnit (pullback q η[A'])).left ≫ (𝟙_ (Over (Sp k))).hom :=
    (Over.w _).symm
  rw [h2]
  exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
end GlobalTheory.CompanionTheory.KerPull.Kernel
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatBoundedAcyclicBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjFlat

theorem acyclic_extendScalars_of_bounded_flat : ∀ (R K : Type) [CommRing R] [CommRing K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p)) (hac : C.Acyclic), (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic :=
  fun _ _ _ _ χ C n hn hflat hac => GlobalTheory.AbLaw.acyclic_extendScalars_of_flat χ C n hn hflat hac

end GlobalTheory.CompanionTheory.PointSurjFlat
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatCoverBaseChangeProduct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem isPullback_snd_lift_fst_snd_comp {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (snd A X).left (lift (fst A X) (snd A X ≫ q)).left q.left (snd A Y).left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact (IsPullback.of_right hout e₂ hY).flip

theorem lift_fst_snd_comp_flat_lfp_surjective :
    ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    Flat (lift (fst A X) (snd A X ≫ q)).left ∧ LocallyOfFinitePresentation (lift (fst A X) (snd A X ≫ q)).left ∧
      Surjective (lift (fst A X) (snd A X ≫ q)).left := by
  intro S A X Y _ _ q hf hl hs
  have h := isPullback_snd_lift_fst_snd_comp A X Y q
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) h hf,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hl,
    MorphismProperty.of_isPullback (P := @Surjective) h hs⟩

end GlobalTheory.CompanionTheory.RigDesc
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnits
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FnDesc

theorem exists_app_eq_of_lfp {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] (U : Y.Opens) (f : Γ(X, π ⁻¹ᵁ U))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (π ⁻¹ᵁ U))
      (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)), g₁ ≫ π = g₂ ≫ π →
      (g₁.appLE _ ⊤ h₁).hom f = (g₂.appLE _ ⊤ h₂).hom f) :
    ∃ a, (π.app U).hom a = f := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have p := isPullback_morphismRestrict π U
  have : Flat (π ∣_ U) := MorphismProperty.of_isPullback (P := @Flat) p.flip ‹_›
  have : LocallyOfFinitePresentation (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) p.flip ‹_›
  obtain ⟨b, hb⟩ := GlobalTheory.FunDescent.exists_appTop_eq (π ∣_ U) ((GlobalTheory.FunDescent.res (π ⁻¹ᵁ U)).hom f) (by
    intro Z g₁ g₂ e
    have k : ∀ g : Z ⟶ (π ⁻¹ᵁ U).toScheme, ⊤ ≤ (g ≫ (π ⁻¹ᵁ U).ι) ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      intro g; simp
    have := hf Z (g₁ ≫ (π ⁻¹ᵁ U).ι) (g₂ ≫ (π ⁻¹ᵁ U).ι) (k _) (k _) (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e])
    rw [← GlobalTheory.FunDescent.res_comp_appTop _ g₁ _ rfl, ← GlobalTheory.FunDescent.res_comp_appTop _ g₂ _ rfl] at this
    exact this)
  obtain ⟨a, rfl⟩ := (GlobalTheory.FunDescent.res_bijective U).2 b
  refine ⟨a, (GlobalTheory.FunDescent.res_bijective _).1 ?_⟩
  rw [← GlobalTheory.FunDescent.res_square_apply, hb]

theorem units_descend :
    ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f → ∀ V : Q.Opens,
    Function.Injective (pullU f V) ∧ ∀ a : Γ(P, f ⁻¹ᵁ V)ˣ,
      (∀ (W : Scheme.{0}) (b c : W ⟶ P), b ≫ f = c ≫ f → ∀ w : W, f (b w) ∈ V →
        gm b w (f ⁻¹ᵁ V) a = gm c w (f ⁻¹ᵁ V) a) → ∃ s : Γ(Q, V)ˣ, pullU f V s = a := by
  intro P Q f _ _ _ V
  refine ⟨fun a b h => Units.ext (GlobalTheory.FunDescent.app_injective f V (congrArg Units.val h)), fun a ha => ?_⟩
  obtain ⟨t, ht⟩ := exists_app_eq_of_lfp f V a.val (fun Z g₁ g₂ h₁ h₂ e => by
    have k : ∀ (g : Z ⟶ P) (h : ⊤ ≤ g ⁻¹ᵁ (f ⁻¹ᵁ V)) (z : Z),
        gm (𝟙 Z) z ⊤ (res h (pullU g _ a)) = gm g z (f ⁻¹ᵁ V) a := fun g h z =>
      (gm_res (𝟙 Z) z h trivial _).trans ((gm_pull (𝟙 Z) g z _ (h trivial) _).trans (by
        rw [Category.id_comp]))
    have : res h₁ (pullU g₁ _ a) = res h₂ (pullU g₂ _ a) := unit_ext fun z _ =>
      (k g₁ h₁ z).trans ((ha Z g₁ g₂ e z (h₁ trivial)).trans (k g₂ h₂ z).symm)
    exact congrArg Units.val this)
  obtain ⟨s, rfl⟩ := GlobalTheory.FunDescent.isUnit_of_isUnit_app f V t (ht ▸ a.isUnit)
  exact ⟨s, Units.ext ht⟩

end GlobalTheory.CompanionTheory.FnDesc
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeneratorDescentUnitExists
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem exists_unit_of_gen : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P), M.IsLB →
    ∀ (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])), c.IsGen →
    ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∃ (u : Γ(pullback (g ≫ f) (g ≫ f), ⊤)) (hu : IsUnit u),
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (w : W) (J : (W ⟶ P) → M.ι), Good M w J →
        gm (pullback.lift a b hab) w ⊤ hu.unit =
          val τ a w J * val c (pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab)) w J * (val τ b w J)⁻¹ := by
  intro Z P Q g f M hM c hc τ hτ
  have hm : (pullback.fst (g ≫ f) (g ≫ f) ≫ g) ≫ f = (pullback.snd (g ≫ f) (g ≫ f) ≫ g) ≫ f := by
    simpa using pullback.condition (f := g ≫ f) (g := g ≫ f)
  let m : pullback (g ≫ f) (g ≫ f) ⟶ pullback f f := pullback.lift _ _ hm
  have m₁ : m ≫ pullback.fst f f = pullback.fst (g ≫ f) (g ≫ f) ≫ g := pullback.lift_fst _ _ hm
  have m₂ : m ≫ pullback.snd f f = pullback.snd (g ≫ f) (g ≫ f) ≫ g := pullback.lift_snd _ _ hm
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, m₁, m₂]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ (LB.pullGen M _ _ τ (pullback.fst (g ≫ f) (g ≫ f))) (LB.pullGen M _ _ c m))
      (LB.invGen M _ _ (LB.pullGen M _ _ τ (pullback.snd (g ≫ f) (g ≫ f)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _) (DVR.pullGen_isGen _ _ _ _ hc _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have le : (⊤ : (pullback (g ≫ f) (g ≫ f)).Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → (pullback (g ≫ f) (g ≫ f) ⟶ P)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, Units.isUnit _, fun W a b hab w J hJ => ?_⟩
  have e₁ : pullback.lift a b hab ≫ pullback.fst (g ≫ f) (g ≫ f) = a := pullback.lift_fst _ _ _
  have e₂ : pullback.lift a b hab ≫ pullback.snd (g ≫ f) (g ≫ f) = b := pullback.lift_snd _ _ _
  have e₃ : pullback.lift a b hab ≫ m = pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab) := by
    apply pullback.hom_ext
    · rw [Category.assoc, m₁, ← Category.assoc, e₁, pullback.lift_fst]
    · rw [Category.assoc, m₂, ← Category.assoc, e₂, pullback.lift_snd]
  rw [IsUnit.unit_of_val_units]
  refine ((gm_res _ w le trivial _).trans (val_of t _ w J PEmpty.elim (fun k => k.elim)).symm).trans ?_
  rw [hv W _ w J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, e₁, e₂, e₃]

end GlobalTheory.CompanionTheory.RigDesc
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExists
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SecNorm

theorem exists_gen_normalised_along : ∀ {X Y S₀ : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K K₂ : Type} [Fintype K] [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ₂ : K₂ → (S₀ ⟶ X)) (ε₂ : K₂ → ℤ) (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 S₀ → FormEq (fun k => e ≫ φ k) ε φ₂ ε₂ →
    ∀ (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen → ∀ (R : LB.Gen (LB.LinComb M φ₂ ε₂)), R.IsGen →
    ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (s : Z ⟶ S₀) (z : Z) (J : (Z ⟶ X) → M.ι), Good M z J → val t' (s ≫ e) z J = val R s z J := by
  intro X Y S₀ M hM K K₂ _ _ φ ε φ₂ ε₂ p e he hF t ht R hR
  obtain ⟨t', ht', hv⟩ := exists_gen hM (φ' := φ) (ε' := ε)
    (fun U _ h => by
      have c := hF U (fun ψ => h (p ≫ ψ))
      simp only [Category.assoc] at c
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.assoc, c.symm]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ t (LB.invGen M _ _ (LB.pullGen M _ _ t (p ≫ e))))
      (LB.pullGen M _ _ R p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hR _))
  refine ⟨t', ht', fun Z s z J hJ => ?_⟩
  have h₁ : (s ≫ e) ≫ p = s := by rw [Category.assoc, he, Category.comp_id]
  have h₂ : (s ≫ e) ≫ p ≫ e = s ≫ e := by rw [← Category.assoc, h₁]
  rw [hv Z (s ≫ e) z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, h₁, h₂, mul_inv_cancel,
    _root_.one_mul]

end GlobalTheory.CompanionTheory.SecNorm
end

