module

public import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
public import Mathlib

@[expose] public section

noncomputable section

open scoped BigOperators Classical Pointwise

namespace Formalism.InvariantFactorPaths.G0

open Formalism.G0

def InvariantFactorsSubmodule : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] [Module R X]
    (π : R) (M M' P : Submodule R X) (g E : ℕ), P ≤ M' → M' ≤ M →
    AllButLE π M P g E → AllButLE π M' P g E

def InvShift : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] [Module R X]
    (π : R) (A B NA NB : Submodule R X) (g E e : ℕ), B ≤ A → NA ≤ A → π ^ e • NA ≤ NB → NB ≤ B →
    AllButLE π A NA g E → AllButLE π B NB g (E + e)

end Formalism.InvariantFactorPaths.G0
