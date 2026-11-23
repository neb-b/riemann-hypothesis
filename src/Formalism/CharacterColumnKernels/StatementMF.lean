module

public import Formalism.CharacterColumnKernels.Statement
public import Formalism.CharacterColumnKernels.StatementX

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

universe u

def epsImg (O : Type*) {OO M : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M]
    [Module OO M] [Module O M] [IsScalarTower O OO M] (ε : OO) : Submodule O M :=
  LinearMap.range (DistribSMul.toLinearMap O M ε)

def epsIdeal (O : Type*) {OO : Type*} [CommRing O] [Ring OO] [Algebra O OO] (ε : OO) :
    Submodule O OO :=
  LinearMap.range (LinearMap.mulLeft O ε)

abbrev EpsDual (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
    (ε : OO) : Type _ :=
  epsIdeal O ε →ₗ[O] Q

section EpsDual
variable (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
  (ε : OO)

end EpsDual

def StatMatlis : Prop :=
  ∀ (O N : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup N]
    [Module O N], IsFiniteLength O N →
    Module.length O (N →ₗ[O] KO O) = Module.length O N

end Formalism.NG
