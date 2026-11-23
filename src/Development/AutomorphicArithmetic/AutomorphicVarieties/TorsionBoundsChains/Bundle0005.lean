module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FinGroup
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.finGroup :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ),
      CardLe (HZ S (j + 1)) (Nat.card S ^ (Nat.card S ^ (j + 1))) := by
  intro S _ _ j
  have hi : Function.Injective (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hq : Function.Surjective (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    fun x => groupHomology_induction_on x fun y => ⟨y, rfl⟩
  have h := subquot (Fin (j + 1) → S) (groupHomology.cycles (Rep.trivial ℤ S ℤ) (j + 1))
    (HZ S (j + 1)) (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom
    (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom (Nat.card S)
    Nat.card_pos hi hq (kill S j)
  rwa [Nat.card_fun, Nat.card_fin] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Imports
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.base :
    ∀ (G X Y : Type) [Group G] [MulAction G X] (M : Rep ℤ G) (e : permRep G X ⟶ M)
      (d : (Y →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ)) (A b : ℕ), Function.Surjective e.hom → Function.Exact d e.hom →
      OrbLe G X A → 1 ≤ b → (∀ y, l1 (d (Finsupp.single y 1)) ≤ b) →
      TorsLe (groupHomology M 0) (b ^ A) := by
  intro G X Y _ _ M e d A b hsurj hex hA hb hd
  set S : Set (X →₀ ℤ) := Set.range (fun y => d (Finsupp.single y 1)) with hS
  have hspan : Submodule.span ℤ S = LinearMap.range d := by
    have h1 : S = d '' Set.range (fun y : Y => Finsupp.single y (1 : ℤ)) := by
      rw [hS, ← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, ← Submodule.map_top]
    congr 1
    have := (Finsupp.basisSingleOne (R := ℤ) (ι := Y)).span_eq
    rw [Finsupp.coe_basisSingleOne] at this
    exact this
  have hker : ∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S := by
    intro f
    rw [hspan, LinearMap.mem_range]
    exact (hex f).trans Set.mem_range
  obtain ⟨φ⟩ := hZero G X M e S hsurj hker
  have hL : ∀ x ∈ Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel G X)) '' S, l1 x ≤ b := by
    rintro x ⟨s, ⟨y, rfl⟩, rfl⟩
    exact (l1_mapDomain_le_and_l1_faceD_single_le.1 _ _ _ _).trans (hd y)
  have hT := cokerTors (MulAction.orbitRel.Quotient G X) A b _ hA hb hL
  exact transport.1 _ _ φ.symm _ hT
end

