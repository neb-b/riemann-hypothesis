module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.CupProducts.Projection
public import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
public import GroundTheory.ProfiniteCohomology.ClassFormations.Corestriction
public import GroundTheory.ProfiniteCohomology.Bundle0008
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.H0IsoHomCohomologyClassZero
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderBound
public import GroundTheory.TateCohomology.InfRes

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section Comp

variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

def contCharComp (χ : Additive G →ₜ+ QZ) (φ : H →* G) (hφ : Continuous φ) : Additive H →ₜ+ QZ :=
  χ.comp ⟨MonoidHom.toAdditive φ, hφ⟩

@[simp]
theorem contCharComp_apply (χ : Additive G →ₜ+ QZ) (φ : H →* G) (hφ : Continuous φ) (x : H) :
    contCharComp χ φ hφ (Additive.ofMul x) = χ (Additive.ofMul (φ x)) :=
  rfl

end Comp

section Naturality

variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

def trivialIntResHom (φ : H →* G) : Rep.res φ (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ H ℤ :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem cohomologyMapAlong_charClassProf (φ : H →* G) (hφ : Continuous φ) (χ : Additive G →ₜ+ QZ) :
    (cohomologyMapAlong φ hφ (trivialIntResHom φ) 2).hom (charClassProf χ) =
      charClassProf (contCharComp χ φ hφ) := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_charClassProf χ
  obtain ⟨w', hw', hwc'⟩ := exists_cocycle_charClassProf (contCharComp χ φ hφ)
  rw [← hw, ← hw', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cocyclesMapAlong]
  funext v
  rw [hwc', hwc]
  rfl

theorem cohomologyMapAlong_cupCharClassProf (φ : H →* G) (hφ : Continuous φ) {A : Rep ℤ G}
    {B : Rep ℤ H} [IsDiscreteRep A] [IsDiscreteRep B] (f : Rep.res φ A ⟶ B) (χ : Additive G →ₜ+ QZ)
    (a : A.ρ.invariants) (b : B.ρ.invariants) (hab : (b : B) = f.hom (a : A)) :
    (cohomologyMapAlong φ hφ f 2).hom ((cupCharClassProf A χ).hom a) =
      (cupCharClassProf B (contCharComp χ φ hφ)).hom b := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  obtain ⟨w', hw', hwc'⟩ := exists_cocycle_cupCharClassProf B (contCharComp χ φ hφ) b
  rw [← hw, ← hw', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cocyclesMapAlong]
  funext v
  rw [hwc', hwc, hab]
  exact map_zsmul f.hom.toAddMonoidHom _ _

end Naturality

section CoresH0

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G) (A : Rep.{0} k G)

def coindConst (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ.invariants :=
  ⟨⟨fun _ => a.1, fun u _ => (a.2 u).symm⟩, fun _ => rfl⟩

noncomputable def invariantsNorm (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    A.ρ.invariants :=
  ((Rep.invariantsFunctor k G).map (coindTrace (U : Subgroup G) A)).hom (coindConst U A a)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
theorem coe_invariantsNorm (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (invariantsNorm U A a : A) = ∑ c : G ⧸ (U : Subgroup G), A.ρ c.out (a : A) := by
  change (coindTrace (U : Subgroup G) A).hom (coindConst U A a).1 = _
  rw [coindTrace_hom_apply]
  rfl

variable [IsDiscreteRep A]

theorem cohomologyCores_H0Iso_inv (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (cohomologyCores U A 0).hom ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a) =
      (H0Iso A).inv.hom (invariantsNorm U A a) := by
  have hs : (shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom
      ((H0Iso (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))).inv.hom
        (coindConst U A a)) = (H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a := by
    have e := H0Iso_hom_cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
      (coindEvalOne (U : Subgroup G) (Rep.res (U : Subgroup G).subtype A))
      ((H0Iso (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))).inv.hom
        (coindConst U A a))
    rw [H0Iso_hom_inv_apply] at e
    rw [← H0Iso_inv_hom_apply (Rep.res (U : Subgroup G).subtype A)
      ((shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom _)]
    congr 1
    exact Subtype.ext e
  rw [← hs]
  have hinv : ∀ x, (inv (shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0)).hom
      ((shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom x) = x := fun x => by
    rw [← ModuleCat.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply]
  change (cohomologyMap (coindTrace (U : Subgroup G) A) 0).hom
    ((inv (shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0)).hom
      ((shapiroMap U (Rep.res (U : Subgroup G).subtype A) 0).hom _)) = _
  rw [hinv, cohomologyMap_zero_H0Iso_inv]
  rfl

end CoresH0

section Projection

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : OpenSubgroup G)


omit [IsTopologicalGroup G] [CompactSpace G] in
theorem coindTrace_naturality {k : Type} [CommRing k] [(U : Subgroup G).FiniteIndex]
    {A B : Rep.{0} k G} (φ : A ⟶ B) :
    Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ) ≫
        coindTrace (U : Subgroup G) B =
      coindTrace (U : Subgroup G) A ≫ φ := by
  ext f
  change (coindTrace (U : Subgroup G) B).hom
      ((Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ)).hom f) =
    φ.hom ((coindTrace (U : Subgroup G) A).hom f)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coindTrace_hom_apply, coindTrace_hom_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [coindTraceTerm_apply, coindTraceTerm_apply]
    change B.ρ x (φ.hom (f.1 x⁻¹)) = φ.hom (A.ρ x (f.1 x⁻¹))
    rw [Rep.hom_comm_apply]

theorem cohomologyMap_cohomologyCores {k : Type} [CommRing k] {A B : Rep.{0} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (φ : A ⟶ B) (n : ℕ) (x : cohomology (Rep.res (U : Subgroup G).subtype A) n) :
    (cohomologyMap φ n).hom ((cohomologyCores U A n).hom x) =
      (cohomologyCores U B n).hom
        ((cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n).hom x) := by
  have key : cohomologyCores U A n ≫ cohomologyMap φ n =
      cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n ≫ cohomologyCores U B n := by
    rw [cohomologyCores, cohomologyCores, Category.assoc, ← cohomologyMap_comp,
      ← coindTrace_naturality, cohomologyMap_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, shapiroMap_naturality]
  exact ConcreteCategory.congr_hom key x

theorem cohomologyCores_cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ)
    (a : (Rep.res (U : Subgroup G).subtype A).ρ.invariants) :
    (cohomologyCores U A 2).hom ((cupCharClassProf (Rep.res (U : Subgroup G).subtype A)
        (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))).hom a) =
      (cupCharClassProf A χ).hom (invariantsNorm U A a) := by
  have hres : charClassProf (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _)) =
      (cohomologyRes (Rep.trivial ℤ G ℤ) (U : Subgroup G) 2).hom (charClassProf χ) :=
    (cohomologyMapAlong_charClassProf (U : Subgroup G).subtype (continuous_subgroup_subtype _) χ).symm
  have : IsDiscreteRep (Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) :=
    isDiscreteRep_res_subtype _ _
  have : IsDiscreteRep (Rep.res (U : Subgroup G).subtype A ⊗
      Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) := isDiscreteRep_tensor _ _
  have hρ : ∀ x : cohomology (Rep.res (U : Subgroup G).subtype A ⊗
      Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) 2,
      (cohomologyMap (ρ_ (Rep.res (U : Subgroup G).subtype A)).hom 2).hom x =
        (cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map (ρ_ A).hom) 2).hom
          ((cohomologyMap (resTensorIso (U : Subgroup G).subtype A (Rep.trivial ℤ G ℤ)).inv 2).hom x) :=
    fun x => ConcreteCategory.congr_hom (cohomologyMap_comp
      (resTensorIso (U : Subgroup G).subtype A (Rep.trivial ℤ G ℤ)).inv
      ((Rep.resFunctor (U : Subgroup G).subtype).map (ρ_ A).hom) 2) x
  change (cohomologyCores U A 2).hom ((cohomologyMap (ρ_ (Rep.res (U : Subgroup G).subtype A)).hom 2).hom
      (cup (zero_add 2) ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a)
        (charClassProf (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))))) =
    (cohomologyMap (ρ_ A).hom 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom (invariantsNorm U A a))
      (charClassProf χ))
  rw [hres]
  change (cohomologyCores U A 2).hom ((cohomologyMap (ρ_ (Rep.res (U : Subgroup G).subtype A)).hom 2).hom
      (cup (B := Rep.res (U : Subgroup G).subtype (Rep.trivial ℤ G ℤ)) (zero_add 2)
        ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a)
        ((cohomologyRes (Rep.trivial ℤ G ℤ) (U : Subgroup G) 2).hom (charClassProf χ)))) =
    (cohomologyMap (ρ_ A).hom 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom (invariantsNorm U A a))
      (charClassProf χ))
  rw [hρ, ← cohomologyMap_cohomologyCores]
  have hp := cohomologyCores_cup_cohomologyRes U (A := A) (B := Rep.trivial ℤ G ℤ) (zero_add 2)
    ((H0Iso (Rep.res (U : Subgroup G).subtype A)).inv.hom a) (charClassProf χ)
  rw [cohomologyCores_H0Iso_inv] at hp
  exact congrArg (cohomologyMap (ρ_ A).hom 2).hom hp

end Projection

section Formation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (C : Rep ℤ G)

def invariantsSubgroupOf {U V : OpenSubgroup G} (_h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    (Rep.res (openSubgroupOf U V : Subgroup (U : Subgroup G)).subtype
      (Rep.res (U : Subgroup G).subtype C)).ρ.invariants :=
  ⟨a.1, fun w => a.2 ⟨w.1.1, w.2⟩⟩

noncomputable def invariantsNormLE {U V : OpenSubgroup G} (h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    (Rep.res (U : Subgroup G).subtype C).ρ.invariants :=
  invariantsNorm (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) (invariantsSubgroupOf C h a)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
theorem coe_invariantsNormLE {U V : OpenSubgroup G} (h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    (invariantsNormLE C h a : C) =
      ∑ c : (U : Subgroup G) ⧸ (openSubgroupOf U V : Subgroup (U : Subgroup G)), C.ρ c.out (a : C) :=
  coe_invariantsNorm _ _ _

variable [IsDiscreteRep C]

theorem ClassFormation.inv_cupCharClassProf_invariantsNormLE (F : ClassFormation C)
    (χ : Additive G →ₜ+ QZ) {U V : OpenSubgroup G} (h : V ≤ U)
    (a : (Rep.res (V : Subgroup G).subtype C).ρ.invariants) :
    F.inv U ((cupCharClassProf (Rep.res (U : Subgroup G).subtype C)
        (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))).hom
          (invariantsNormLE C h a)) =
      F.inv V ((cupCharClassProf (Rep.res (V : Subgroup G).subtype C)
        (contCharComp χ (V : Subgroup G).subtype (continuous_subgroup_subtype _))).hom a) := by
  rw [← F.inv_cohomologyCoresLE h, cohomologyCoresLE_eq, ModuleCat.hom_comp, LinearMap.comp_apply,
    cohomologyMapAlong_cupCharClassProf _ _ _ _ a (invariantsSubgroupOf C h a) rfl]
  have hχ : contCharComp (contCharComp χ (V : Subgroup G).subtype (continuous_subgroup_subtype _))
      (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
        (continuous_subgroupOfEquivOfLe _) =
      contCharComp (contCharComp χ (U : Subgroup G).subtype (continuous_subgroup_subtype _))
        (openSubgroupOf U V : Subgroup (U : Subgroup G)).subtype (continuous_subgroup_subtype _) := by
    ext x
    rfl
  rw [hχ, cohomologyCores_cupCharClassProf]
  rfl

end Formation

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderInfRes
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits

universe u

section Tower

theorem additive_units_ext {M : Type u} [Field M] {x y : Additive Mˣ}
    (h : ((Additive.toMul x : Mˣ) : M) = ((Additive.toMul y : Mˣ) : M)) : x = y :=
  Additive.toMul.injective (Units.ext h)

variable (K F M : Type u) [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M] [Algebra F M]
  [IsScalarTower K F M]

def galRestrictScalars : Gal(M/F) →* Gal(M/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

theorem galRestrictScalars_injective : Function.Injective (galRestrictScalars K F M) :=
  fun _ _ h => AlgEquiv.ext fun x => DFunLike.congr_fun h x

def unitsResScalarsHom :
    Rep.res (galRestrictScalars K F M) (galUnits.{u} K M) ⟶ galUnits.{u} F M :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

noncomputable def unitsRes (n : ℕ) :
    groupCohomology (galUnits.{u} K M) n ⟶ groupCohomology (galUnits.{u} F M) n :=
  groupCohomology.map (galRestrictScalars K F M) (unitsResScalarsHom K F M) n

variable [Normal K F]

noncomputable def unitsInclHom :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F) (galUnits.{u} K F) ⟶
      galUnits.{u} K M :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Fˣ) (B := Additive Mˣ)
    (MonoidHom.toAdditive (Units.map ((algebraMap F M : F →+* M) : F →* M))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)⟩

noncomputable def unitsInfl (n : ℕ) :
    groupCohomology (galUnits.{u} K F) n ⟶ groupCohomology (galUnits.{u} K M) n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom F) (unitsInclHom K F M) n

variable [FiniteDimensional K M] [IsGalois K M]

noncomputable abbrev galFixing : Subgroup Gal(M/K) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F).ker

omit [FiniteDimensional K M] [IsGalois K M] in
theorem mem_galFixing_iff (σ : Gal(M/K)) :
    σ ∈ galFixing K F M ↔ ∀ x : F, σ (algebraMap F M x) = algebraMap F M x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    rw [← AlgEquiv.restrictNormal_commutes σ F x]
    change algebraMap F M ((AlgEquiv.restrictNormalHom F σ) x) = _
    rw [h]
    rfl
  · intro h
    ext x
    apply (algebraMap F M).injective
    change algebraMap F M ((AlgEquiv.restrictNormal σ F) x) = _
    rw [AlgEquiv.restrictNormal_commutes, h]
    rfl

omit [FiniteDimensional K M] [IsGalois K M] in
theorem range_galRestrictScalars : (galRestrictScalars K F M).range = galFixing K F M := by
  ext σ
  rw [mem_galFixing_iff]
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

noncomputable def galFixingEquiv : Gal(M/F) ≃* galFixing K F M :=
  (MonoidHom.ofInjective (galRestrictScalars_injective K F M)).trans
    (MulEquiv.subgroupCongr (range_galRestrictScalars K F M))


noncomputable def galFixingCohomologyIso (n : ℕ) :
    groupCohomology (galUnits.{u} F M) n ≅
      groupCohomology (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) n :=
  groupCohomology.mapIso (galFixingEquiv K F M) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

omit [FiniteDimensional K M] [IsGalois K M] in
theorem unitsRes_eq (n : ℕ) :
    unitsRes K F M n = GroundTheory.GroupCoh.restriction (galUnits.{u} K M) (galFixing K F M) n ≫
      (galFixingCohomologyIso K F M n).inv := by
  have hinv : (galFixingCohomologyIso K F M n).inv = groupCohomology.map
      (galFixingEquiv K F M : Gal(M/F) →* galFixing K F M)
      (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩ : Rep.res (galFixingEquiv K F M : Gal(M/F) →* _)
        (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) ⟶ galUnits.{u} F M) n := rfl
  rw [hinv, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · ext σ x
    rfl
  · rfl

omit [IsGalois K M] in
theorem isZero_groupCohomology_one_galFixing :
    IsZero (groupCohomology (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) 1) := by
  have : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite K F M
  exact (isZero_groupCohomology_one_galUnits F M).of_iso (galFixingCohomologyIso K F M 1).symm

noncomputable def unitsToInvariantsTower :
    Additive Fˣ →ₗ[ULift.{u} ℤ]
      Representation.invariants ((galUnits.{u} K M).ρ.comp (galFixing K F M).subtype) :=
  LinearMap.codRestrict _ (unitsInclHom K F M).hom.toLinearMap fun x σ => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (mem_galFixing_iff K F M σ.1).1 σ.2 _

theorem unitsToInvariantsTower_bijective : Function.Bijective (unitsToInvariantsTower K F M) := by
  have : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite K F M
  have : IsGalois F M := IsGalois.tower_top_of_isGalois K F M
  constructor
  · intro x y h
    have h' := congrArg (fun v => ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M)) h
    apply Additive.toMul.injective
    apply Units.ext
    exact (algebraMap F M).injective h'
  · intro v
    have hfix : ∀ τ : Gal(M/F), τ ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M) =
        ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M) := by
      intro τ
      have := v.2 ⟨galRestrictScalars K F M τ, (range_galRestrictScalars K F M) ▸ ⟨τ, rfl⟩⟩
      exact congrArg (fun w => ((Additive.toMul (α := Mˣ) w : Mˣ) : M)) this
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed _).2 hfix)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Additive.toMul (α := Mˣ) v.1).ne_zero hy.symm
    refine ⟨Additive.ofMul (Units.mk0 y hy0), Subtype.ext ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    exact hy

noncomputable def unitsInvariantsEquivTower :
    Additive Fˣ ≃ₗ[ULift.{u} ℤ]
      Representation.invariants ((galUnits.{u} K M).ρ.comp (galFixing K F M).subtype) :=
  LinearEquiv.ofBijective _ (unitsToInvariantsTower_bijective K F M)

noncomputable def galQuotientEquiv : Gal(M/K) ⧸ galFixing K F M ≃* Gal(F/K) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (AlgEquiv.restrictNormalHom_surjective M)

noncomputable def galQuotientCohomologyIso (n : ℕ) :
    groupCohomology (galUnits.{u} K F) n ≅
      groupCohomology ((galUnits.{u} K M).quotientToInvariants (galFixing K F M)) n :=
  groupCohomology.mapIso (galQuotientEquiv K F M).symm (unitsInvariantsEquivTower K F M) (fun g => by
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) M g
    have hq : (galQuotientEquiv K F M).symm (AlgEquiv.restrictNormalHom F σ) =
        (σ : Gal(M/K) ⧸ galFixing K F M) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hq]
    refine LinearMap.ext fun x => Subtype.ext (additive_units_ext ?_)
    exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)) n

theorem unitsInfl_eq (n : ℕ) :
    unitsInfl K F M n = (galQuotientCohomologyIso K F M n).hom ≫
      GroundTheory.GroupCoh.inflation (galUnits.{u} K M) (galFixing K F M) n := by
  have hhom : (galQuotientCohomologyIso K F M n).hom = groupCohomology.map
      (galQuotientEquiv K F M : Gal(M/K) ⧸ galFixing K F M →* Gal(F/K))
      (Rep.ofHom ⟨(unitsInvariantsEquivTower K F M).toLinearMap, fun g => by
        obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
        refine LinearMap.ext fun x => Subtype.ext (additive_units_ext ?_)
        exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)⟩ :
        Rep.res (galQuotientEquiv K F M : Gal(M/K) ⧸ galFixing K F M →* Gal(F/K))
          (galUnits.{u} K F) ⟶ (galUnits.{u} K M).quotientToInvariants (galFixing K F M)) n := rfl
  rw [hhom, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · ext σ x
    rfl
  · rfl

theorem unitsInfl_two_injective : Function.Injective (unitsInfl K F M 2).hom := by
  rw [unitsInfl_eq, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (GroundTheory.GroupCoh.inflation_two_injective (A := galUnits.{u} K M) (S := galFixing K F M)
    (isZero_groupCohomology_one_galFixing K F M)).comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

theorem range_unitsInfl_two_eq_ker_unitsRes :
    LinearMap.range (unitsInfl K F M 2).hom = LinearMap.ker (unitsRes K F M 2).hom := by
  have hsurj : Function.Surjective (galQuotientCohomologyIso K F M 2).hom.hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinj : Function.Injective (galFixingCohomologyIso K F M 2).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [unitsInfl_eq, unitsRes_eq, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 hsurj, Submodule.map_top, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot]
  exact GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := galUnits.{u} K M)
    (S := galFixing K F M) (isZero_groupCohomology_one_galFixing K F M)

end Tower

section Count

variable (K E F M : Type u) [Field K] [Field E] [Field F] [Field M] [Algebra K E] [Algebra K F]
  [Algebra K M] [Algebra E M] [Algebra F M] [IsScalarTower K E M] [IsScalarTower K F M]
  [Normal K E] [Normal K F] [FiniteDimensional K M] [IsGalois K M]

theorem natCard_le_of_unitsInfl_comp_unitsRes_eq_zero
    (h : unitsInfl K E M 2 ≫ unitsRes K F M 2 = 0)
    [Finite (groupCohomology (galUnits.{u} K F) 2)] :
    Nat.card (groupCohomology (galUnits.{u} K E) 2) ≤
      Nat.card (groupCohomology (galUnits.{u} K F) 2) := by
  have hmem : ∀ y, (unitsInfl K E M 2).hom y ∈ LinearMap.range (unitsInfl K F M 2).hom := by
    intro y
    rw [range_unitsInfl_two_eq_ker_unitsRes, LinearMap.mem_ker]
    exact congrArg (fun φ => φ.hom y) h
  choose g hg using hmem
  refine Nat.card_le_card_of_injective g fun y y' hyy' => ?_
  apply unitsInfl_two_injective K E M
  rw [← hg y, ← hg y', hyy']

end Count

end GroundTheory.ProfCoh
end

