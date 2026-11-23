module

public import Formalism.PeriodIntegrals.HasseOrdBd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Bundle0001

@[expose] public section

theorem hasse_order_bound : PI.HasseOrdBd :=
  PI.HasseOrdBdW.hasseOrdBd_of PI.HasseOrdBdW.compositionalInverseSymm PI.HasseOrdBdW.orthogonalSplitPolarizationVanishes PI.HasseOrdBdW.addPreservesExpCongruence
    PI.HasseOrdBdW.expCongruenceExtendsToSum
