module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.LevGap

open NumberField Formalism.UG Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]

def diagMap (a : n → E) : (n → 𝓞 E) →ₗ[𝓞 E] (n → E) where
  toFun x := fun i => a i * (x i : E)
  map_add' x y := by
    funext i
    simp [mul_add]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
    ring

@[simp] theorem diagMap_apply (a : n → E) (x : n → 𝓞 E) (i : n) :
    diagMap a x i = a i * (x i : E) := rfl

def diagLat (a : n → E) : Submodule (𝓞 E) (n → E) := LinearMap.range (diagMap a)

theorem mem_diagLat {a : n → E} {x : n → E} :
    x ∈ diagLat a ↔ ∀ i, ∃ c : 𝓞 E, x i = a i * (c : E) := by
  constructor
  · rintro ⟨c, rfl⟩ i
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    exact ⟨c, funext fun i => (hc i).symm⟩

theorem single_mem_diagLat (a : n → E) (i : n) : Pi.single i (a i) ∈ diagLat a := by
  refine mem_diagLat.2 fun j => ?_
  by_cases h : j = i
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

theorem hform_one (σ : E →+* E) (x y : n → E) : hform σ 1 x y = ∑ i, σ (x i) * y i := by
  unfold hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable (σ : E →+* E)

theorem map_int_mem (c : 𝓞 E) : σ (c : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom σ c, rfl⟩

theorem mem_dualSet_diagLat {a : n → E} {y : n → E} :
    y ∈ dualSet σ 1 (diagLat a) ↔ ∀ i, σ (a i) * y i ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro h i
    have h1 := h _ (single_mem_diagLat a i)
    rw [hform_one, Finset.sum_eq_single i] at h1
    · simpa using h1
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rintro h _ ⟨c, rfl⟩
    rw [hform_one]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [diagMap_apply, map_mul, mul_right_comm]
    exact Subring.mul_mem _ (h i) (map_int_mem σ (c i))

theorem dualSet_diagLat {a : n → E} (ha : ∀ i, a i ≠ 0) :
    dualSet σ 1 (diagLat a) = (diagLat fun i => (σ (a i))⁻¹ : Set (n → E)) := by
  ext y
  rw [mem_dualSet_diagLat σ, SetLike.mem_coe, mem_diagLat]
  refine forall_congr' fun i => ?_
  have h0 : σ (a i) ≠ 0 := (map_ne_zero σ).2 (ha i)
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [RingOfIntegers.coe_eq_algebraMap, hc]; field_simp⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, RingOfIntegers.coe_eq_algebraMap]; field_simp⟩

end General

section LatT

variable {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]

def vecAt (i0 : n) (z : E) : n → E := Function.update (fun _ => (1 : E)) i0 z

@[simp] theorem vecAt_same (i0 : n) (z : E) : vecAt i0 z i0 = z := Function.update_self ..

theorem vecAt_ne {i0 i : n} (h : i ≠ i0) (z : E) : vecAt i0 z i = 1 :=
  Function.update_of_ne h ..

theorem vecAt_ne_zero {i0 : n} {z : E} (hz : z ≠ 0) (i : n) : vecAt i0 z i ≠ 0 := by
  by_cases h : i = i0
  · subst h
    simpa using hz
  · rw [vecAt_ne h]
    exact one_ne_zero

def latT (i0 : n) (pz : 𝓞 E) : Submodule (𝓞 E) (n → E) := diagLat (vecAt i0 (pz : E))

theorem mem_latT {i0 : n} {pz : 𝓞 E} {x : n → E} :
    x ∈ latT i0 pz ↔ (∃ c : 𝓞 E, x i0 = (pz : E) * (c : E)) ∧
      ∀ i, i ≠ i0 → x i ∈ (algebraMap (𝓞 E) E).range := by
  rw [latT, mem_diagLat]
  constructor
  · intro h
    refine ⟨by simpa using h i0, fun i hi => ?_⟩
    obtain ⟨c, hc⟩ := h i
    exact ⟨c, by rw [hc, vecAt_ne hi, one_mul]⟩
  · rintro ⟨h0, h1⟩ i
    by_cases hi : i = i0
    · subst hi
      simpa using h0
    · obtain ⟨c, hc⟩ := h1 i hi
      exact ⟨c, by rw [vecAt_ne hi, one_mul, ← hc]⟩

variable (σ : E →+* E) {i0 : n} {pz : 𝓞 E} {T : ℕ}

theorem dualSet_latT (hz : (pz : E) ≠ 0) :
    dualSet σ 1 (latT i0 pz) = (diagLat (vecAt i0 (σ (pz : E))⁻¹) : Set (n → E)) := by
  rw [latT, dualSet_diagLat σ (vecAt_ne_zero hz)]
  congr 2
  funext i
  by_cases hi : i = i0
  · subst hi
    simp
  · simp [vecAt_ne hi]

theorem span_dualSet_latT (hz : (pz : E) ≠ 0) :
    Submodule.span (𝓞 E) (dualSet σ 1 (latT i0 pz)) = diagLat (vecAt i0 (σ (pz : E))⁻¹) := by
  rw [dualSet_latT σ hz, Submodule.span_eq]

end LatT

section Bridge

open Formalism.MainNotions.Gaps.LG

variable {E : Type} [Field E] [NumberField E]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

end Bridge

section Record

open Formalism.MainNotions.Gaps.LG

theorem finrank_hostE_eq {R : Ranks} (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField, Ranks.f, Ranks.n]
  ring

end Record

end Formalism.MainNotions.Gaps.LevGap

end
