module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

noncomputable section

open CategoryTheory UpperTheory.V.KL

namespace UpperTheory.V.Published

def KStability : Prop :=
  ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i n : ℕ, 2 * i + s + 2 ≤ n →
    IsIso (grpHMap (stab R n (n + 1) (Nat.le_succ n)) i)

end UpperTheory.V.Published

end
