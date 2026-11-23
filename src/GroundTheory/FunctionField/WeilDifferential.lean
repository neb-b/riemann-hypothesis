module

public import Mathlib
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.FunctionField.PlaceBasic
public import GroundTheory.FunctionField.Bundle0001
public import GroundTheory.FunctionField.Divisor
public import GroundTheory.FunctionField.DivisorDegree
public import GroundTheory.FunctionField.Repartition
public import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL

@[expose] public section

namespace GroundTheory.FunctionField

open Module Repartition

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

namespace Divisor

theorem A_sup_le (D E : Divisor k K) : A (D ⊔ E) ≤ A D ⊔ A E := by
  classical
  intro a ha
  let f : Place k K → K := fun v => if E v ≤ D v then a v else 0
  have hf : {v : Place k K | f v ∉ v.ring}.Finite :=
    a.finite_not_mem.subset fun v (hv : f v ∉ v.ring) => by
      show a v ∉ v.ring
      intro h
      apply hv
      simp only [f]
      split_ifs
      · exact h
      · exact v.ring.zero_mem
  let b := Repartition.mk f hf
  have hb : b ∈ A D := by
    intro v
    change v.valuation (f v) ≤ _
    simp only [f]
    split_ifs with h
    · have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_left h] at this
    · rw [map_zero]; exact zero_le
  have hc : a - b ∈ A E := by
    intro v
    rw [Repartition.sub_apply]
    change v.valuation (a v - f v) ≤ _
    simp only [f]
    split_ifs with h
    · rw [sub_self, map_zero]; exact zero_le
    · rw [sub_zero]
      have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_right (not_le.1 h).le] at this
  have : a = b + (a - b) := by abel
  rw [this]
  exact Submodule.add_mem_sup hb hc

noncomputable def weilSpace (D : Divisor k K) : Submodule k (Module.Dual k (Repartition k K)) :=
  (A D ⊔ principal k K).dualAnnihilator

theorem mem_weilSpace {D : Divisor k K} {ω : Module.Dual k (Repartition k K)} :
    ω ∈ weilSpace D ↔ (∀ a ∈ A D, ω a = 0) ∧ ∀ x : K, ω (diag x) = 0 := by
  rw [weilSpace, Submodule.mem_dualAnnihilator]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha),
      fun x => h _ (Submodule.mem_sup_right (diag_mem_principal x))⟩
  · rintro ⟨h1, h2⟩ a ha
    obtain ⟨b, hb, c, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
    rw [map_add (f := _), h1 b hb, h2 x, add_zero]

theorem weilSpace_anti {D E : Divisor k K} (h : D ≤ E) : weilSpace E ≤ weilSpace D :=
  Submodule.dualAnnihilator_anti (sup_le_sup_right (A_mono h) _)

theorem weilSpace_sup {D E : Divisor k K} {ω : Module.Dual k (Repartition k K)}
    (hD : ω ∈ weilSpace D) (hE : ω ∈ weilSpace E) : ω ∈ weilSpace (D ⊔ E) := by
  rw [mem_weilSpace] at hD hE ⊢
  refine ⟨fun a ha => ?_, hD.2⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 (A_sup_le D E ha)
  rw [map_add (f := _), hD.1 b hb, hE.1 c hc, add_zero]

theorem finrank_weilSpace (D : Divisor k K) : finrank k (weilSpace D) = indexOfSpeciality D := by
  change finrank k (A D ⊔ principal k K).dualAnnihilator = _
  rw [indexOfSpeciality,
    ← (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).finrank_eq,
    Subspace.dual_finrank_eq]

theorem exists_indexOfSpeciality_eq_zero :
    ∃ c : ℤ, ∀ D : Divisor k K, c ≤ deg D → indexOfSpeciality D = 0 := by
  obtain ⟨E₀, hE₀⟩ := exists_eq_genusInt (k := k) (K := K)
  refine ⟨deg E₀ + genusInt k K, fun D hD => ?_⟩
  have h1 := le_genusInt (D - E₀)
  rw [map_sub] at h1
  have hpos : 0 < finrank k (L (D - E₀)) := by
    have : (0 : ℤ) < finrank k (L (D - E₀)) := by linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0 : (z : K) ≠ 0 := fun h => hz (Subtype.ext h)
  have hzL := (mem_L_iff_le hz0).1 z.2
  have hle : E₀ ≤ D + divisor (z : K) := by
    rw [← sub_nonneg]
    convert hzL using 1
    abel
  have hD' := eq_genusInt_of_le hE₀ hle
  rw [finrank_L_add_divisor D hz0, map_add (f := _), deg_divisor, add_zero] at hD'
  have hi := indexOfSpeciality_eq_genusInt D
  have : (indexOfSpeciality D : ℤ) = 0 := by linarith
  exact_mod_cast this

theorem exists_indexOfSpeciality_pos : ∃ D : Divisor k K, 0 < indexOfSpeciality D := by
  obtain ⟨P⟩ := Place.nonempty (k := k) (K := K)
  set N : ℕ := (2 - genusInt k K).toNat with hN
  refine ⟨-(N • Finsupp.single P 1), ?_⟩
  have h := indexOfSpeciality_eq_genusInt (-(N • Finsupp.single P 1) : Divisor k K)
  have hdeg : deg (-(N • Finsupp.single P 1) : Divisor k K) = -(N * P.deg) := by
    rw [map_neg, map_nsmul, deg_single, nsmul_eq_mul, one_mul]
  have hP : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hN' : (2 : ℤ) - genusInt k K ≤ N := Int.self_le_toNat _
  have hl : (0 : ℤ) ≤ finrank k (L (-(N • Finsupp.single P 1) : Divisor k K)) := Nat.cast_nonneg _
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg _
  have : (1 : ℤ) ≤ indexOfSpeciality (-(N • Finsupp.single P 1) : Divisor k K) := by
    rw [h, hdeg]
    nlinarith
  exact_mod_cast this

end Divisor

open Divisor


variable (k K) in
def weilDifferentials : Submodule k (Module.Dual k (Repartition k K)) where
  carrier := {ω | ∃ D : Divisor k K, ω ∈ weilSpace D}
  add_mem' := by
    rintro ω₁ ω₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    exact ⟨D₁ ⊓ D₂, add_mem (weilSpace_anti inf_le_left h₁) (weilSpace_anti inf_le_right h₂)⟩
  zero_mem' := ⟨0, zero_mem _⟩
  smul_mem' := by
    rintro c ω ⟨D, h⟩
    exact ⟨D, Submodule.smul_mem _ c h⟩


variable (k K) in
def WeilDifferential : Type _ := weilDifferentials k K

namespace WeilDifferential

instance : AddCommGroup (WeilDifferential k K) :=
  inferInstanceAs (AddCommGroup (weilDifferentials k K))

instance : Module k (WeilDifferential k K) := inferInstanceAs (Module k (weilDifferentials k K))

def toDual : WeilDifferential k K →ₗ[k] Module.Dual k (Repartition k K) :=
  (weilDifferentials k K).subtype

theorem toDual_injective : Function.Injective (toDual (k := k) (K := K)) :=
  Subtype.val_injective

def mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    WeilDifferential k K :=
  (⟨ω, h⟩ : weilDifferentials k K)

@[simp]
theorem toDual_mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    toDual (mk ω h) = ω :=
  rfl

theorem exists_mem (ω : WeilDifferential k K) : ∃ D : Divisor k K, toDual ω ∈ weilSpace D :=
  (show weilDifferentials k K from ω).2

theorem exists_ne_zero : ∃ ω : WeilDifferential k K, ω ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_indexOfSpeciality_pos (k := k) (K := K)
  rw [← finrank_weilSpace] at hD
  have hne : weilSpace D ≠ ⊥ := by
    intro h
    rw [h] at hD
    simp at hD
  obtain ⟨φ, hφmem, hφ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨mk φ ⟨D, hφmem⟩, fun h => hφ ?_⟩
  have := congrArg toDual h
  rwa [toDual_mk, map_zero] at this

noncomputable def toQuotDual (D : Divisor k K) :
    weilSpace D ≃ₗ[k] Module.Dual k (Repartition k K ⧸ (A D ⊔ principal k K)) :=
  (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).symm

theorem exists_deg_lt {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ c : ℤ, ∀ D : Divisor k K, toDual ω ∈ weilSpace D → deg D < c := by
  obtain ⟨c, hc⟩ := exists_indexOfSpeciality_eq_zero (k := k) (K := K)
  refine ⟨c, fun D hD => ?_⟩
  by_contra hle
  push Not at hle
  have h0 : finrank k (Repartition k K ⧸ (A D ⊔ principal k K)) = 0 := hc D hle
  have hsub : Subsingleton (Repartition k K ⧸ (A D ⊔ principal k K)) :=
    Module.finrank_zero_iff.1 h0
  have h1 : toQuotDual D ⟨toDual ω, hD⟩ = 0 :=
    LinearMap.ext fun q => by simp [Subsingleton.elim q 0]
  have h2 : (⟨toDual ω, hD⟩ : weilSpace D) = 0 :=
    (toQuotDual D).injective (by rw [h1, map_zero])
  exact hω (toDual_injective (by rw [map_zero]; exact congrArg Subtype.val h2))

theorem exists_divisor {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ W : Divisor k K, ∀ D : Divisor k K, toDual ω ∈ weilSpace D ↔ D ≤ W := by
  classical
  obtain ⟨c, hc⟩ := exists_deg_lt hω
  obtain ⟨D₀, hD₀⟩ := ω.exists_mem
  obtain ⟨n, ⟨W, hW, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun n => ∃ D, toDual ω ∈ weilSpace D ∧ deg D = n)
      ⟨c, fun n ⟨D, hD, hn⟩ => hn ▸ (hc D hD).le⟩ ⟨deg D₀, D₀, hD₀, rfl⟩
  refine ⟨W, fun D => ⟨fun hD => ?_, fun h => weilSpace_anti h hW⟩⟩
  have hsup := weilSpace_sup hD hW
  have h1 := hmax _ ⟨_, hsup, rfl⟩
  have h2 : 0 ≤ (D ⊔ W) - W := sub_nonneg.2 le_sup_right
  have h3 : deg ((D ⊔ W) - W) = 0 := by
    have := deg_nonneg h2
    rw [map_sub] at this ⊢
    linarith
  have h4 := eq_zero_of_deg_eq_zero h2 h3
  have : D ⊔ W = W := sub_eq_zero.1 h4
  rw [← this]
  exact le_sup_left


open Classical in
noncomputable def divisor (ω : WeilDifferential k K) : Divisor k K :=
  if h : ω = 0 then 0 else Classical.choose (exists_divisor h)

end WeilDifferential

end GroundTheory.FunctionField
