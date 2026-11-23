module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlaceBelowAllPowers

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X) (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y)

def PartBAt (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (φ : G D.host.E N.Om →* (X.Ok i k)ˣ) (e : ℝ) : Prop :=
  IsLatIn (eThPsi Y i j b k Q φ (SgJ Y E i j b)) (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) ∧
    IdxAt Y i j b (SgJ Y E i j b) k Q φ e ∧ InclAt Y i j b (SgJ Y E i j b) k Q φ

variable {Y bkP E}

end GlobalTheory.IndefiniteRowSideFullHecke.PlaceBelowAllPowers

end
