module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle0002

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

section Line

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

theorem exists_line_of_add_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (h₃ : W.toAffine.Nonsingular x₃ y₃)
    (hs : Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0) :
    ∃ ℓ ν : F, y₁ = ℓ * x₁ + ν ∧ y₂ = ℓ * x₂ + ν ∧ y₃ = ℓ * x₃ + ν ∧
      x₁ + x₂ + x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * ℓ * ν - W.a₁ * ν - W.a₃ * ℓ ∧
      x₁ * x₂ * x₃ = ν ^ 2 + W.a₃ * ν - W.a₆ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
    intro hxy
    rw [Point.add_of_Y_eq hxy.1 hxy.2, zero_add] at hs
    exact Point.some_ne_zero _ hs
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  rw [Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at hs
  obtain ⟨hx3, hy3⟩ := hs
  rw [← hℓ] at hx3 hy3
  refine ⟨ℓ, y₁ - ℓ * x₁, by ring, ?_, ?_, ?_⟩
  · by_cases hx : x₁ = x₂
    · subst hx
      have hy := Y_eq_of_Y_ne h₁.1 h₂.1 rfl (fun h => hxy ⟨rfl, h⟩)
      rw [← hy]; ring
    · rw [hℓ, slope_of_X_ne hx]
      have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
      field_simp
      ring
  · rw [← W.toAffine.negY_negY x₃ y₃, ← hy3, ← hx3]
    simp only [addY, negY_negY, negAddY]
    ring
  have e := W.toAffine.addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj, Cubic.toPoly_injective,
    Cubic.mk.injEq, hx3] at e
  obtain ⟨-, e2, e3, e4⟩ := e
  rw [← hℓ] at e2 e3 e4
  refine ⟨by linear_combination e2, by linear_combination -e3, by linear_combination e4⟩

end Line

section Counting

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G)

end Counting

section DVR

open IsLocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)


section Origin

variable {π : 𝒪} (hπ : Irreducible π)
include hπ





end Origin



end DVR

end

end GroundTheory.Arith.Abelian
end

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilFixedField
section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

theorem translate_inj {S S' : W.toAffine.Point} (h : translate W S = translate W S') : S = S' := by
  have e := congrArg (fun ψ => Point.map ψ (genericPoint W)) h
  simp only [map_translate_genericPoint, add_right_inj] at e
  exact Point.map_injective (W' := W) (f := Algebra.ofId F W.toAffine.FunctionField) e

end GroundTheory.Arith.Abelian
end

