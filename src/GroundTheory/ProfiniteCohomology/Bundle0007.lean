module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.Procyclic
public import GroundTheory.ProfiniteCohomology.Characters
public import GroundTheory.ProfiniteCohomology.Bundle0005
public import GroundTheory.ProfiniteCohomology.CupProducts
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
public import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.CohomologyTwoIntAddEquivQZSymmApply
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

theorem isAddTorsion_QZ : IsAddTorsion QZ := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q.den, q.den_pos, ?_⟩
  change ((q.den • q : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨q.num, ?_⟩
  rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num, zsmul_one]

section Eval

variable {G : Type*} [Group G] [TopologicalSpace G]

end Eval

section H2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {σ : G}

end H2

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.CyclicCupGaloisDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

noncomputable def cupRightProf (h : p + q = n) (b : cohomology B q) :
    cohomology A p ⟶ cohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cup h).flip b)

theorem cupRightProf_apply (h : p + q = n) (b : cohomology B q) (a : cohomology A p) :
    (cupRightProf h b).hom a = cup h a b :=
  rfl

end Generic

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

noncomputable def charClassProf (χ : Additive G →ₜ+ QZ) : cohomology (Rep.trivial ℤ G ℤ) 2 :=
  (δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom ((cohomologyOneRatModIntIso G).inv.hom χ)

noncomputable def cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ) :=
  (H0Iso A).inv ≫ cupRightProf (A := A) (B := Rep.trivial ℤ G ℤ) (zero_add 2) (charClassProf χ) ≫
    cohomologyMap (A := A ⊗ Rep.trivial ℤ G ℤ) (B := A) (ρ_ A).hom 2

end Profinite

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L]

def unitsInvariant (a : Kˣ) : (galUnitsZ K L).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) a), fun σ => by
    apply Additive.toMul.injective
    apply Units.ext
    change ((galUnitsHom K L σ (Units.map (algebraMap K L : K →* L) a) : Lˣ) : L) =
      (Units.map (algebraMap K L : K →* L) a : L)
    rw [coe_galUnitsHom_apply]
    simp⟩

@[simp]
theorem coe_unitsInvariant (a : Kˣ) :
    ((Additive.toMul (unitsInvariant K L a : Additive Lˣ) : Lˣ) : L) = algebraMap K L a :=
  rfl

variable [IsGalois K L]

noncomputable def galCupClass (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    cohomology (galUnitsZ K L) 2 :=
  (cupCharClassProf (galUnitsZ K L) χ).hom (unitsInvariant K L a)

end Galois

end GroundTheory.ProfCoh
end

