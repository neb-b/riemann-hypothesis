module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.Bundle0001

@[expose] public section

open NumberField IsDedekindDomain

namespace PI.UnipApproxD

def AddDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F))

end PI.UnipApproxD
