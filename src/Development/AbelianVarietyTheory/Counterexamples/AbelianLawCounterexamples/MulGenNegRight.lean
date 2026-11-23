module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.TrivialBiextension

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

universe u

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BiextSignTwist

section
variable {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

end

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev lamφ : ULift.{u} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) :=
  fun I => (psum G (x2 G) I.down).left

def LawIsCube (L : RigLB G) (c : CubicalStr G L)
    (ψ : ULift.{u} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (law : LB.Gen (LB.LinComb (abelian₂ G L.L) ψ lawε)) : Prop :=
  ∀ (J : ULift.{u} (Fin 3) → ULift.{u} (Finset (Fin 2)) → L.L.ι) (j : thK → L.L.ι),
    (∀ k I k' I', ψ k ≫ lamφ G I = ψ k' ≫ lamφ G I' → J k I = J k' I') →
    LB.Coh L.L (thφ G (x3 G)) j →
    (∀ k I I', ψ k ≫ lamφ G I = thφ G (x3 G) I' → J k I = j I') →
    res (inf_le_left : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (law.s J) =
    res (inf_le_right : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (c.t.s j)

section Trivial
open GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension (trivLB pull_one mul_one' corr_one isGen_one)

end Trivial

end GlobalTheory.BiextSignTwist
