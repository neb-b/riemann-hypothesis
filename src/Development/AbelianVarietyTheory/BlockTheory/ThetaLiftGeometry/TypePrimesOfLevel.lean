module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


end Generic

variable (D : D7)


def TypePrimesLarge : Prop := ∀ i, 2 * D.R.f * D.R.k + 1 < D.host.g i

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

end
