module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeModel

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

def pts {T : Over S} (a b c : T ⟶ A) : Fin 8 → (T.left ⟶ A.left) :=
  fun k ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left

theorem comp_pts {T Z : Over S} (w : Z ⟶ T) (a b c : T ⟶ A) (k : Fin 8) :
    w.left ≫ pts a b c k = pts (w ≫ a) (w ≫ b) (w ≫ c) k := by
  refine (Over.comp_left _ _ _ w _).symm.trans (congrArg (fun q : Z ⟶ A ↦ q.left) ?_)
  fin_cases k <;> simp [MonObj.comp_mul]

theorem prod_pts {T : Over S} (a b c : T ⟶ A) (h : a = 1 ∨ b = 1 ∨ c = 1) (U : Type) [CommGroup U]
    (k : (T.left ⟶ A.left) → U) :
    ∏ i, k (pts a b c i) ^ (![1, -1, -1, -1, 1, 1, 1, -1] : Fin 8 → ℤ) i = 1 := by
  rcases h with rfl | rfl | rfl <;>
  · simp only [Fin.prod_univ_eight, pts, _root_.one_mul, _root_.mul_one, Matrix.cons_val, zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

end GlobalTheory.CubeModel
