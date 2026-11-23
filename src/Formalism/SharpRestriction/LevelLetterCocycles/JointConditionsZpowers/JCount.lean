module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

variable (D : D7) {Dall Dgood : ℕ}

def CountCylAt (A : AllRowsAt D Dall Dgood) (c₃ : ℝ) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    |(A.dimT (cyl D k S) : ℝ) -
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) *
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))

end Formalism.MainNotions.N.CylinderCountFamily
