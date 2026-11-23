module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulLawsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationEtaleTorsion


variable {S : Scheme.{0}}

theorem mulN_eq_mulA (A : Over S) [GrpObj A] (n : ℕ) : mulN A n = mulA A n := by
  rw [mulA, ← comp_mulN, Category.id_comp]

theorem finrank_mulN_eq_card (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    [IsFinite (mulN A n).left] [Etale (mulN A n).left] [Surjective (mulN A n).left]
    {k : Type} [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ A.left)
    (z : Spec (CommRingCat.of k)) :
    (mulN A n).left.finrank (t z) =
      Nat.card {y : Over.mk (t ≫ A.hom) ⟶ A // y ^ n = 1} := by
  obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank (mulN A n).left t z
  have h1 : 1 ≤ (mulN A n).left.finrank (t z) :=
    (Scheme.Hom.one_le_finrank_iff_surjective (mulN A n).left).2 inferInstance _
  rw [← hc] at h1 ⊢
  let t' : Over.mk (t ≫ A.hom) ⟶ A := Over.homMk t rfl
  let E : {x : Spec (CommRingCat.of k) ⟶ A.left // x ≫ (mulN A n).left = t} ≃
      {y : Over.mk (t ≫ A.hom) ⟶ A // y ^ n = t'} :=
    { toFun := fun x => ⟨Over.homMk x.1 (by
          have := x.2 =≫ A.hom
          rw [Category.assoc, Over.w] at this
          exact this), by
        rw [← comp_mulN]
        ext
        exact x.2⟩
      invFun := fun y => ⟨y.1.left, by
        have := y.2
        rw [← comp_mulN] at this
        exact congrArg (fun f => f.left) this⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨x₀⟩ := (Nat.card_pos_iff.1 h1).1
  obtain ⟨y₀, hy₀⟩ := E x₀
  rw [Nat.card_congr E]
  refine Nat.card_congr ((Equiv.mulRight y₀⁻¹).subtypeEquiv fun y => ?_)
  rw [Equiv.coe_mulRight, mul_pow, inv_pow, hy₀, mul_inv_eq_one]

end GlobalTheory.MulLawsCompare
