module

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators
open Module

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

theorem rat_four_sq (p : ℚ) (hp : 0 ≤ p) : ∃ a b c d : ℚ, p = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨x, y, z, w, hs⟩ := Nat.sum_four_squares (p.num.toNat * p.den)
  refine ⟨x / p.den, y / p.den, z / p.den, w / p.den, ?_⟩
  have hnum : (0 : ℤ) ≤ p.num := Rat.num_nonneg.mpr hp
  have hd : (p.den : ℚ) ≠ 0 := by positivity
  have hn : ((p.num.toNat : ℕ) : ℚ) = (p.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hnum
  have key : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 + (z : ℚ) ^ 2 + (w : ℚ) ^ 2 = (p.num : ℚ) * p.den := by
    have h1 : ((x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 : ℕ) : ℚ) = ((p.num.toNat * p.den : ℕ) : ℚ) := by rw [hs]
    push_cast at h1
    rw [h1, hn]
  calc p = (p.num : ℚ) / p.den := (Rat.num_div_den p).symm
    _ = ((p.num : ℚ) * p.den) / (p.den : ℚ) ^ 2 := by field_simp
    _ = _ := by rw [← key]; field_simp

variable {K : Type} [Field K]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)

structure Herm4 : Prop where
  add_left : ∀ x x' y, h (x + x') y = h x y + h x' y
  smul_left : ∀ (k : K) x y, h (k • x) y = k * h x y
  symm : ∀ x y, h y x = c (h x y)
  pos : ∀ x, x ≠ 0 → h x x ≠ 0 ∧ ∃ p q r s : K, c p = p ∧ c q = q ∧ c r = r ∧ c s = s ∧
    h x x = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2

variable {c h}

def Herm4.hl (H : Herm4 c h) (y : V) : V →ₗ[K] K where
  toFun x := h x y
  map_add' x x' := H.add_left x x' y
  map_smul' k x := H.smul_left k x y

theorem Herm4.linInd (H : Herm4 c h) {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hv0 : ∀ i, v i ≠ 0)
    (hv : ∀ i j, i ≠ j → h (v i) (v j) = 0) : LinearIndependent K v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : H.hl (v i) (∑ j ∈ s, g j • v j) = 0 := by rw [hg, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single i] at h1
  · exact (mul_eq_zero.mp h1).resolve_right (H.pos (v i) (hv0 i)).1
  · intro j _ hji
    show g j * h (v j) (v i) = 0
    rw [hv j i hji, mul_zero]
  · intro his
    exact absurd hi his

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

end
