module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle0003
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle0002

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.SingularCubic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

section Generic

variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}

theorem map_add_of_triple {G : Type*} [AddCommGroup G] (Φ : V.toAffine.Point → G) (h0 : Φ 0 = 0)
    (hneg : ∀ P, Φ (-P) = -Φ P)
    (htri : ∀ {x₁ y₁ x₂ y₂ x₃ y₃ : F} (h₁ : V.toAffine.Nonsingular x₁ y₁)
      (h₂ : V.toAffine.Nonsingular x₂ y₂) (h₃ : V.toAffine.Nonsingular x₃ y₃),
      Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0 →
        Φ (.some _ _ h₁) + Φ (.some _ _ h₂) + Φ (.some _ _ h₃) = 0)
    (P Q : V.toAffine.Point) : Φ (P + Q) = Φ P + Φ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change Φ (0 + Q) = Φ 0 + Φ Q; rw [zero_add, h0, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change Φ (_ + 0) = _ + Φ 0; rw [add_zero, h0, add_zero]
  set S := Point.some _ _ h₁ + Point.some _ _ h₂ with hS
  rcases hSc : S with _ | ⟨x₃, y₃, h₃⟩
  · have hQ : Point.some _ _ h₂ = -Point.some _ _ h₁ := by
      have : S = 0 := hSc
      rw [hS] at this
      exact eq_neg_of_add_eq_zero_right this
    change Φ 0 = _
    rw [h0, hQ, hneg, add_neg_cancel]
  · have hn := (nonsingular_neg (W' := V.toAffine) x₃ y₃).2 h₃
    have ht := htri h₁ h₂ hn (by
      have e : (Point.some _ _ hn : V.toAffine.Point) = -Point.some _ _ h₃ := by
        rw [Point.neg_some]
      rw [e, ← hSc, hS]; abel)
    have e : (Point.some _ _ hn : V.toAffine.Point) = -Point.some _ _ h₃ := by
      rw [Point.neg_some]
    rw [e, hneg, add_neg_eq_zero] at ht
    exact ht.symm

end Generic

section Origin

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0)
include h3 h4 h6

theorem origin_eq {x y : F} (h : V.toAffine.Equation x y) :
    y ^ 2 + V.a₁ * x * y - V.a₂ * x ^ 2 = x ^ 3 := by
  rw [equation_iff, h3, h4, h6] at h
  linear_combination h

theorem origin_x_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  subst hx
  have he := origin_eq V h3 h4 h6 h.1
  have hy : y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linear_combination he)
  subst hy
  have := (nonsingular_zero (W := V.toAffine)).1 h
  rcases this.2 with h' | h'
  · exact h' h3
  · exact h' h4

theorem origin_nonsingular {x y : F} (h : V.toAffine.Equation x y) (hx : x ≠ 0) :
    V.toAffine.Nonsingular x y := by
  rw [nonsingular_iff']
  refine ⟨h, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hA, hB⟩ := hc
  have he := origin_eq V h3 h4 h6 h
  rw [h4] at hA
  rw [h3] at hB
  apply hx
  apply pow_eq_zero_iff (n := 3) (by norm_num) |>.1
  linear_combination (-x) * hA + (-y) * hB + 2 * he

end Origin

section Cusp

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) (α : F) (h1 : V.a₁ = -2 * α) (h2 : V.a₂ = -α ^ 2)

def cuspMap : V.toAffine.Point → F
  | 0 => 0
  | .some x y _ => x / (y - α * x)

include h3 h4 h6 h1 h2

theorem cusp_eq {x y : F} (h : V.toAffine.Equation x y) : (y - α * x) ^ 2 = x ^ 3 := by
  have := origin_eq V h3 h4 h6 h
  rw [h1, h2] at this
  linear_combination this

theorem cusp_den_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : y - α * x ≠ 0 := by
  intro h0
  apply origin_x_ne_zero V h3 h4 h6 h
  have := cusp_eq V h3 h4 h6 α h1 h2 h.1
  rw [h0] at this
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 (by linear_combination -this)

theorem cuspMap_neg (P : V.toAffine.Point) : cuspMap V α (-P) = -cuspMap V α P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [cuspMap]; rfl
  · rw [Point.neg_some]
    simp only [cuspMap, negY, h1, h3]
    rw [show -y - -2 * α * x - 0 - α * x = -(y - α * x) by ring, div_neg]

theorem cuspMap_triple {x₁ y₁ x₂ y₂ x₃ y₃ : F} (g₁ : V.toAffine.Nonsingular x₁ y₁)
    (g₂ : V.toAffine.Nonsingular x₂ y₂) (g₃ : V.toAffine.Nonsingular x₃ y₃)
    (hs : Point.some _ _ g₁ + Point.some _ _ g₂ + Point.some _ _ g₃ = 0) :
    cuspMap V α (.some _ _ g₁) + cuspMap V α (.some _ _ g₂) + cuspMap V α (.some _ _ g₃) = 0 := by
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_line_of_add_eq_zero g₁ g₂ g₃ hs
  have d1 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₁
  have d2 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₂
  have d3 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₃
  simp only [cuspMap]
  rw [div_add_div _ _ d1 d2, div_add_div _ _ (mul_ne_zero d1 d2) d3, div_eq_zero_iff]
  left
  rw [h1, h2] at v1
  rw [h1, h3, h4] at v2
  rw [h3, h6] at v3
  rw [l1, l2, l3]
  linear_combination 3 * (ℓ - α) ^ 2 * v3 + 2 * (ℓ - α) * ν * v2 + ν ^ 2 * v1

def cuspHom : V.toAffine.Point →+ F :=
  AddMonoidHom.mk' (cuspMap V α) (map_add_of_triple (cuspMap V α) rfl
    (cuspMap_neg V h3 h4 h6 α h1 h2) (cuspMap_triple V h3 h4 h6 α h1 h2))

end Cusp

section Node

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) {L : Type*} [Field L] [Algebra F L] (α β : L)
  (hs : algebraMap F L V.a₁ = -(α + β)) (hp : algebraMap F L V.a₂ = -(α * β))

include h3 h4 h6 hs hp

end Node

section NodeSplit

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) (α β : F) (hs : algebraMap F F V.a₁ = -(α + β))
  (hp : algebraMap F F V.a₂ = -(α * β))
include h3 h4 h6 hs hp

end NodeSplit

section Torus

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) {L : Type*} [Field L] [Algebra F L] (α β : L)
  (hs : algebraMap F L V.a₁ = -(α + β)) (hp : algebraMap F L V.a₂ = -(α * β)) (σ : L ≃ₐ[F] L)

include h3 h4 h6 hs hp

end Torus

end

end GroundTheory.Arith.Abelian
end

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilPairing
section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine AddSubgroup

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

theorem divisorOf_pow {f : W.toAffine.FunctionField} (hf : f ≠ 0) (k : ℕ) :
    divisorOf W (f ^ k) = k • divisorOf W f := by
  induction k with
  | zero => rw [pow_zero, divisorOf_one, zero_smul]
  | succ k ih => rw [pow_succ, divisorOf_mul W (pow_ne_zero k hf) hf, ih, succ_nsmul]

theorem divisorOf_prod {ι' : Type*} (s : Finset ι') (φ : ι' → W.toAffine.FunctionField)
    (hφ : ∀ i ∈ s, φ i ≠ 0) : divisorOf W (∏ i ∈ s, φ i) = ∑ i ∈ s, divisorOf W (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, divisorOf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      divisorOf_mul W (hφ a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hφ i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hφ i (Finset.mem_insert_of_mem hi)]



variable {W}

variable (W)

variable {W}


end GroundTheory.Arith.Abelian
end

