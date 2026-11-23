module

public import Mathlib

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

namespace Formalism.MainNotions.DIV.Cons

universe u

attribute [local instance] CategoryTheory.Hom.group

abbrev GrpSch (S : Scheme.{u}) : Type (u + 1) := Grp (Over S)

def nMul {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : A.X ⟶ A.X := (𝟙 A.X) ^ N

def tors {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : Over S :=
  pullback (nMul A N) (MonObj.one : 𝟙_ (Over S) ⟶ A.X)

end Formalism.MainNotions.DIV.Cons
