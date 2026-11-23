module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum

open ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{0}}

structure PowerDatum (j : ℕ) (G' G : Over S) [GrpObj G'] [GrpObj G] where

  pr : Fin j → (G' ⟶ G)

  isMonHom : ∀ i, IsMonHom (pr i)

  bij : ∀ T : Over S, Function.Bijective (fun (x : T ⟶ G') (i : Fin j) => x ≫ pr i)

attribute [instance] PowerDatum.isMonHom

section Power

variable (G : Over S)

variable [GrpObj G]


end Power

section Symm

variable {G : Over S} [GrpObj G]

lemma eSec_inv : eSec G ≫ (GrpObj.inv (X := G)).left = 𝟙 _ ≫ eSec G := by
  rw [Category.id_comp, eSec, ← Over.comp_left]
  congr 1
  simp

variable [IsCommMonObj G]

def IsNormSymm (L : RigLB G) (w : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1)) L.rig
      (rigPullOf (GrpObj.inv (X := G)).left (𝟙 _) eSec_inv L.L L.rig)

end Symm

namespace PowerDatum

variable {j : ℕ} {G' G : Over S} [GrpObj G'] [GrpObj G] (P : PowerDatum j G' G)

variable [IsCommMonObj G'] [IsCommMonObj G]

end PowerDatum

end GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum
