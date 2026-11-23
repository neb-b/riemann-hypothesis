module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.BetaAtInfinityZero
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Bundle0001
public import CompanionTheory.AutomorphicTheory.KFiniteVectors.KDecay
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefEigOfInfChar
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Bundle0001

@[expose] public section

noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP

theorem span_powers : SpanPow := mul_mem_spanBox_of_gap

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end CompanionTheory.LimBd.Main
