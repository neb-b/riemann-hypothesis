module

public import Mathlib
public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.Bundle0002

@[expose] public section

-- bundled from GroundTheory.LocalFields.UnramifiedDefs
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

class IsUnramified (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop where

  ramificationIndex_eq_one : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem isUnramified_iff : IsUnramified K L ↔ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnramified_iff_residueDegree_eq_finrank :
    IsUnramified K L ↔ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L := by
  rw [isUnramified_iff, ← ramificationIndex_mul_residueDegree K L]
  change ramificationIndex K L = 1 ↔ _
  have h := residueDegree_pos K L
  constructor
  · intro h1
    rw [h1, one_mul]
  · intro h1
    have : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = 1 * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
      rw [one_mul]
      exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right h this

theorem isUnramified_iff_finrank_residueField :
    IsUnramified K L ↔ Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  rw [isUnramified_iff_residueDegree_eq_finrank, residueDegree_eq_finrank]

theorem IsUnramified.residueDegree_eq_finrank [IsUnramified K L] :
    ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L :=
  (isUnramified_iff_residueDegree_eq_finrank K L).1 inferInstance

theorem IsUnramified.finrank_residueField [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  (isUnramified_iff_finrank_residueField K L).1 inferInstance

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional L M]

theorem isUnramified_tower_iff :
    IsUnramified K M ↔ IsUnramified K L ∧ IsUnramified L M := by
  simp only [isUnramified_iff, ramificationIndex_tower K L M, mul_eq_one]

end Tower

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.UnramifiedRootsOfUnity
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

section RootsOfUnity

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem exists_pow_eq_one_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {a : 𝓀[L]} (ha : a ^ m = 1) :
    ∃ x : 𝒪[L], x ^ m = 1 ∧ IsLocalRing.residue 𝒪[L] x = a := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hmon : (X ^ m - C (1 : 𝒪[L])).Monic := monic_X_pow_sub_C 1 hm0
  have hev : (X ^ m - C (1 : 𝒪[L])).eval a₀ ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp [ha]
  have hder : IsUnit (Ideal.Quotient.mk 𝓂[L] ((X ^ m - C (1 : 𝒪[L])).derivative.eval a₀)) := by
    have ha0 : IsLocalRing.residue 𝒪[L] a₀ ≠ 0 := by
      rintro h
      rw [h, zero_pow hm0] at ha
      exact zero_ne_one ha
    change IsUnit (IsLocalRing.residue 𝒪[L] _)
    rw [isUnit_iff_ne_zero]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_pow,
      eval_X, eval_natCast, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hm (pow_ne_zero _ ha0)
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian _ hmon a₀ hev hder
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hxa

theorem eq_of_pow_eq_one_of_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {x y : 𝒪[L]}
    (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue 𝒪[L] x = IsLocalRing.residue 𝒪[L] y) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hxu : IsUnit x := (isUnit_pow_iff hm0).mp (hx ▸ isUnit_one)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ m - C 1)
    (by simp [hx]) (by simp [hy]) ?_ ?_
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, h, sub_self]
  · simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_pow, eval_X]
    refine IsUnit.mul ?_ (hxu.pow _)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simpa using hm


omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
theorem mem_integer_of_pow_eq_one {m : ℕ} (hm : m ≠ 0) {x : L} (hx : x ^ m = 1) : x ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff]
  have h : valuation L x ^ m = 1 := by rw [← map_pow, hx, map_one]
  refine le_of_not_gt fun h1 ↦ ?_
  have := one_lt_pow₀ h1 hm
  rw [h] at this
  exact this.false

theorem exists_isPrimitiveRoot_card_residueField_sub_one :
    ∃ ζ : 𝒪[L], IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := 𝓀[L]ˣ)
  have hpg : IsPrimitiveRoot (g : 𝓀[L]) (Nat.card 𝓀[L] - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨x, hx, hxg⟩ :=
    exists_pow_eq_one_residue_eq (natCast_card_residueField_sub_one_ne_zero L) hpg.pow_eq_one
  refine ⟨x, hx, fun l hl ↦ hpg.dvd_of_pow_eq_one l ?_⟩
  rw [← hxg, ← map_pow, hl, map_one]

end RootsOfUnity

section Degree

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natDegree_minpoly_residue_le (x : 𝒪[L]) :
    (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] x)).natDegree ≤ (minpoly K (x : L)).natDegree := by
  have hx : IsIntegral 𝒪[K] (x : L) := (isIntegral_iff K L x).mpr x.2
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, (minpoly.monic hx).natDegree_map]
  set g := minpoly 𝒪[K] (x : L)
  have hg0 : aeval x g = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← minpoly.aeval 𝒪[K] (x : L)]
    exact (aeval_algebraMap_apply L x g).symm
  have hmon : (g.map (algebraMap 𝒪[K] 𝓀[K])).Monic := (minpoly.monic hx).map _
  refine (natDegree_le_natDegree (minpoly.min 𝓀[K] _ hmon ?_)).trans
    ((minpoly.monic hx).natDegree_map _).le
  rw [aeval_map_algebraMap, ← IsLocalRing.ResidueField.algebraMap_eq, aeval_algebraMap_apply, hg0,
    map_zero]

end Degree

end GroundTheory.LocalField
end
end

