module

public import Mathlib

@[expose] public section

open scoped InnerProductSpace Pointwise

noncomputable section

namespace Formalism.DV

def gaussIdeal (σ O : Type) [CommRing O] [IsLocalRing O] : Ideal (MvPolynomial σ O) :=
  Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O)

end Formalism.DV
