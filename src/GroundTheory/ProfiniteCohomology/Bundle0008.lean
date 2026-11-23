module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
public import GroundTheory.ProfiniteCohomology.ClassFormationDefs
public import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
public import GroundTheory.ProfiniteCohomology.ClassFormations.Quotient
public import GroundTheory.ProfiniteCohomology.ClassFormations.Finite
public import GroundTheory.ProfiniteCohomology.Bundle0007
public import GroundTheory.ProfiniteCohomology.CyclicCupInflation
public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle0001
public import GroundTheory.ProfiniteCohomology.CupProducts.GroupCohomology

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.CartierDualDefs
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Iso

variable {k G : Type*} [CommRing k] [Monoid G]

def Rep.isoOfBijective {A B : Rep.{u} k G} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    A ≅ B :=
  Rep.mkIso (Representation.IntertwiningMap.ofBijective f.hom hf)

end Iso

section ZMod

variable (G : Type*) [Monoid G]

abbrev zmodRep (n : ℕ) : Rep.{u} (ULift.{u} ℤ) G :=
  Rep.trivial (ULift.{u} ℤ) G (ULift.{u} (ZMod n))

end ZMod

attribute [local instance 2000] Rep.hV2

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

abbrev cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) : Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  Rep.of (Representation.linHom M.ρ (galUnits.{u} K L).ρ)

variable {K L}

theorem cartierDual_ρ_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (σ : Gal(L/K))
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    ((cartierDual K L M).ρ σ f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m =
      (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ m)) :=
  rfl

variable (K L)

def evalBilin (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M →ₗ[ULift.{u} ℤ] (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) →ₗ[ULift.{u} ℤ] galUnits.{u} K L where
  toFun m :=
    { toFun := fun f => f m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := LinearMap.ext fun f => f.map_add a b
  map_smul' r a := LinearMap.ext fun f => f.map_smul r a

def cartierPairing (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M ⊗ cartierDual K L M ⟶ galUnits.{u} K L :=
  pairingHom (evalBilin K L M) fun σ m f => by
    change (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ (M.ρ σ m))) = (galUnits.{u} K L).ρ σ (f m)
    rw [Representation.inv_self_apply]

variable {K L}

@[simp]
theorem cartierPairing_tmul (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (m : M)
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) :
    (cartierPairing K L M).hom (m ⊗ₜ[ULift.{u} ℤ] (f : cartierDual K L M) :
      (M ⊗ cartierDual K L M : Rep _ _)) = f m :=
  pairingHom_tmul (A := M) (B := cartierDual K L M) (evalBilin K L M) _ m f

variable (K L)

variable {K L}

end GroundTheory.ProfCoh
end
end

-- bundled from GroundTheory.ProfiniteCohomology.ClassFormations
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section QuotQuot

variable {U V V' : Subgroup G} [(V.subgroupOf U).Normal] [(V'.subgroupOf U).Normal]


variable (C : Rep.{u} k G)

variable [IsDiscreteRep C]

end QuotQuot

namespace PreClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

end PreClassFormation

namespace ClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem inv_injective (W : OpenSubgroup G) : Function.Injective (F.inv W) :=
  (F.inv_bijective W).1

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem exists_inv_eq (W : OpenSubgroup G) (q : QZ) : ∃ x : H2Open C W, F.inv W x = q :=
  (F.inv_bijective W).2 q


include hVU in
theorem tate_hypotheses (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V) :=
  F.toPreClassFormation.tate_hypotheses hVU F.inv_injective (F.exists_inv_eq U _) S

end ClassFormation

namespace ClassFormationAt

variable [CompactSpace G] [TotallyDisconnectedSpace G] {P : Set Nat.Primes}
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormationAt P C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F


variable (hP : ∀ p : Nat.Primes, (p : ℕ) ∣ (V : Subgroup G).relIndex U → p ∈ P)


end ClassFormationAt

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.CyclicCupProf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory GroundTheory.GroupCoh

def charAdd {G : Type} [Group G] [TopologicalSpace G] (χ : Additive G →ₜ+ QZ) :
    Additive G →+ AddCircle (1 : ℚ) :=
  QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem charAdd_apply (χ : Additive G →ₜ+ QZ) (x : Additive G) :
    charAdd χ x = QZ.toAddCircle (χ x) :=
  rfl

omit [IsTopologicalGroup G] in
theorem isLocallyConstant_charAdd (χ : Additive G →ₜ+ QZ) :
    IsLocallyConstant fun g : G => charAdd χ (Additive.ofMul g) := by
  have hc : Continuous fun g : G => χ (Additive.ofMul g) :=
    χ.continuous_toFun.comp continuous_ofMul
  have h := IsLocallyConstant.comp_continuous
    (IsLocallyConstant.of_discrete (X := QZ) (fun x : QZ => QZ.toAddCircle x)) hc
  exact h

theorem exists_cocycle_H0Iso_inv {k : Type} [CommRing k] (A : Rep k G) [IsDiscreteRep A]
    (a : A.ρ.invariants) :
    ∃ z : cocycles A 0, cohomologyπ A 0 z = (H0Iso A).inv.hom a ∧
      cochainOf (A := A) (cocycleι (A := A) (p := 0) z) = fun _ => (a : A) := by
  refine ⟨(cocyclesIso₀ A).inv.hom a, rfl, ?_⟩
  have hf : (cocyclesIso₀ A).hom ≫ ModuleCat.ofHom (invariantsToCochains₀ A) =
      (cochainsComplex A).iCycles 0 := by
    dsimp only [cocyclesIso₀, Limits.KernelFork.mapIsoOfIsLimit]
    exact (Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)
  have e := ConcreteCategory.congr_hom hf ((cocyclesIso₀ A).inv a)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at e
  exact (congrArg (cochainOf (A := A)) e).symm

section Cocycles

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

theorem exists_cocycle_charH1 (χ : Additive G →ₜ+ QZ) :
    ∃ z : cocycles (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1,
      cohomologyπ _ 1 z = (cohomologyOneRatModIntIso G).inv.hom χ ∧
      ∀ v : Fin 1 → G, cochainOf (A := Rep.trivial ℤ G (AddCircle (1 : ℚ)))
        (cocycleι (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1 z) v = charAdd χ (Additive.ofMul (v 0)) := by
  obtain ⟨z, hz⟩ := cohomologyπ_surjective _ 1 ((cohomologyOneRatModIntIso G).inv.hom χ)
  refine ⟨z, hz, fun v => ?_⟩
  have h1 : (cohomologyOneRatModIntIso G).hom.hom (cohomologyπ _ 1 z) = χ := by
    rw [hz]
    exact congrArg (fun f => f.hom χ) (cohomologyOneRatModIntIso G).inv_hom_id
  simp only [cohomologyOneRatModIntIso, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    at h1
  change (locallyConstantHomQZEquiv G) ((cohomologyOneIsoOfIsTrivial G (AddCircle (1 : ℚ))).hom.hom
    (cohomologyπ _ 1 z)) = χ at h1
  have h4 := DFunLike.congr_fun h1 (Additive.ofMul (v 0))
  rw [locallyConstantHomQZEquiv_apply] at h4
  have h2 := cohomologyOneIsoOfIsTrivial_hom_cohomologyπ G (AddCircle (1 : ℚ)) z (v 0)
  have hv : v = fun _ => v 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have h5 := congrArg QZ.toAddCircle h4
  rw [AddEquiv.apply_symm_apply] at h5
  rw [charAdd_apply, ← h5]
  conv_lhs => rw [hv]
  exact h2.symm

theorem exists_cocycle_charClassProf (χ : Additive G →ₜ+ QZ) :
    ∃ x : cocycles (Rep.trivial ℤ G ℤ) 2, cohomologyπ _ 2 x = charClassProf χ ∧
      ∀ v : Fin 2 → G, cochainOf (A := Rep.trivial ℤ G ℤ) (cocycleι (Rep.trivial ℤ G ℤ) 2 x) v =
        charCocycle (charAdd χ) (v 0, v 1) := by
  obtain ⟨z, hz, hzv⟩ := exists_cocycle_charH1 χ
  let y : (Fin 1 → G) → ℚ := fun v => reprIco (charAdd χ (Additive.ofMul (v 0)))
  have hy : IsLocallyConstant y :=
    (((isLocallyConstant_charAdd χ).comp_continuous (continuous_apply 0)).comp reprIco)
  let x₂ := mkCochain (A := (ratSES G).X₂) y hy
  have hx₂ : (cochainsMap (ratSES G).g).f 1 x₂ = cocycleι (A := (ratSES G).X₃) (p := 1) z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    exact (coe_reprIco _).trans (hzv v).symm
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d (ratSES_shortExact G) 2 z x₂ hx₂
  refine ⟨x₁, ?_, fun v => ?_⟩
  · rw [charClassProf, ← hz]
    exact (δ_cohomologyπ_of_lift (ratSES_shortExact G) rfl z x₂ hx₂ x₁ hx₁).symm
  · have e := congrArg (fun c => cochainOf (A := (ratSES G).X₂) c v) hx₁
    simp only [cochainOf_cochainsMap_f] at e
    erw [cochainOf_d, d_one_trivial_apply] at e
    have hc := charCocycle_cast (charAdd χ) (v 0) (v 1)
    apply Int.cast_injective (α := ℚ)
    refine e.trans ?_
    rw [hc]
    change reprIco (charAdd χ (Additive.ofMul (v 1))) - reprIco (charAdd χ (Additive.ofMul (v 0 * v 1)))
      + reprIco (charAdd χ (Additive.ofMul (v 0))) = _
    ring

theorem exists_cocycle_cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ)
    (a : A.ρ.invariants) :
    ∃ w : cocycles A 2, cohomologyπ A 2 w = (cupCharClassProf A χ).hom a ∧
      ∀ v : Fin 2 → G, cochainOf (A := A) (cocycleι (A := A) (p := 2) w) v =
        charCocycle (charAdd χ) (v 0, v 1) • (a : A) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv A a
  obtain ⟨x, hx, hxc⟩ := exists_cocycle_charClassProf χ
  let φ : A ⊗ Rep.trivial ℤ G ℤ ⟶ A := (ρ_ A).hom
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap φ) 2 (cupCocycles (zero_add 2) z0 x), ?_, ?_⟩
  · change _ = (cohomologyMap φ 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom a) (charClassProf χ))
    rw [← hz0, ← hx, cup_cohomologyπ]
    exact (ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap φ 2) _).symm
  · intro v
    have e := congrArg (fun ψ => cochainOf (A := A) (ψ.hom (cupCocycles (zero_add 2) z0 x)))
      (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    change cochainOf (A := A) (((cochainsComplex A).iCycles 2).hom _) v = _
    rw [e, cochainOf_cochainsMap_f]
    change φ.hom (cochainOf (A := A ⊗ Rep.trivial ℤ G ℤ)
      (cocycleι (A ⊗ Rep.trivial ℤ G ℤ) 2 (cupCocycles (zero_add 2) z0 x)) v) = _
    rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cupCochain_apply, hz0c]
    erw [hxc, rightUnitor_hom_tmul]
    exact int_smul_eq_zsmul _ _ _

theorem cupCharClassProf_eq_inflation [CompactSpace G] (A : Rep ℤ G) [IsDiscreteRep A]
    (χ : Additive G →ₜ+ QZ) (U : OpenNormalSubgroup G)
    (ψ : Additive (G ⧸ (U : Subgroup G)) →+ AddCircle (1 : ℚ))
    (hψ : charAdd χ = charComp (U : Subgroup G) ψ) (a : A.ρ.invariants) :
    (cupCharClassProf A χ).hom a =
      (inflation A U 2).hom ((cupCharClass (A.quotientToInvariants (U : Subgroup G)) ψ).hom
        (invariantsToQuotient (U : Subgroup G) a)) := by
  have := Fintype.ofFinite (G ⧸ (U : Subgroup G))
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  rw [← hw, cupCharClass_apply_charCocycle]
  change _ = (inflation A U 2).hom ((groupCohomology.π _ 2).hom ((groupCohomology.isoCocycles₂ _).inv _))
  rw [inflation_π]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cyclesMap_inflationCochains]
  funext v
  rw [hwc, groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  rw [hψ]
  rfl

end Cocycles

end Profinite

end GroundTheory.ProfCoh
end

