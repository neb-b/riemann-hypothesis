module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Bundle0002

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def labInd {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (ϖ : L)
    (d : List ℤ) : Formalism.UG.GU σ n → ℂ :=
  Set.indicator {g | ∃ k₁ ∈ Formalism.UG.KU σ n, ∃ k₂ ∈ Formalism.UG.KU σ n,
    ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((k₁ : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) *
        (((k₂ : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)} 1

variable {D : D7}

end GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

end
