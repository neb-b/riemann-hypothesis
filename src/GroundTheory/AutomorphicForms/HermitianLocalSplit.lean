module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0016
public import GroundTheory.AutomorphicForms.HermitianNormLocal
public import GroundTheory.LocalFields.Bundle0003

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open GroundTheory.LocalField ValuativeRel

section Field

variable {F : Type*} [Field F]

def SqNorm (s u : F) : Prop := ∃ x y : F, x ^ 2 - s * y ^ 2 = u

variable (h2 : (2 : F) ≠ 0)
include h2

end Field

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]


end Local

end GroundTheory.Automorphic
