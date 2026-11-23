module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

def lawε : ULift.{u} (Fin 3) → ℤ := fun k => ![1, -1, -1] k.down

def lamφ : ULift.{u} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) :=
  fun I => (psum G (x2 G) I.down).left

def lamε : ULift.{u} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

def trivLB (X : Scheme.{u}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

section
variable {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

lemma pull_one (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (ht : ∀ j, t.s j = 1) (j) : (LB.pullGen L φ ε t h).s j = 1 := by
  unfold LB.pullGen
  dsimp only
  erw [ht]
  exact (congrArg _ (map_one _)).trans (map_one _)

lemma mul_one' (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht : ∀ j, t.s j = 1) (ht' : ∀ j, t'.s j = 1) (j) : (LB.mulGen L φ ε φ' ε' t t').s j = 1 := by
  unfold LB.mulGen
  dsimp only
  erw [ht, ht']
  exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)

lemma corr_one (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht : ∀ j, t.s j = 1) (ht' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' _ _ _
  erw [ht, ht']
  exact (map_one _).trans (map_one _).symm

lemma isGen_one (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen.IsGen (L := LB.LinComb (trivLB X) φ ε) ⟨fun _ => 1⟩ := by
  intro i j
  have hg : (LB.LinComb (trivLB X) φ ε).g i j = 1 :=
    Finset.prod_eq_one fun k _ =>
      (congrArg (· ^ ε k) ((congrArg _ (map_one _)).trans (map_one _))).trans (one_zpow _)
  rw [hg]
  exact (map_one _).trans ((_root_.one_mul _).trans (map_one _)).symm
end

end

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
