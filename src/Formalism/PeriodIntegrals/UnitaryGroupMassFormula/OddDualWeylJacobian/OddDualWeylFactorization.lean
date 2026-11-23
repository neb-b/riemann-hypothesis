module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.RevColOneTranspose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.TransvectionMulApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightMultiplicity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.MnrUpdateEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.AevalMulHomog
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightVectorUnique

@[expose] public section

namespace PI.OddDualWeyl

theorem odd_dual_weyl_factorization {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ)
    (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam :=
  oddDualWeyl_of rowOpIntertwining highest_weight_multiplicity highest_weight_divisibility hermitianDiagonalization lowestWeightMem (highestWeightDual_of jacobiMinorReverse) weight_homomorphism degreeBalance
    evalDuality highest_weight_vector_unique columnSpanDual reverseSignUnit twistedWeylStep O m lam

end PI.OddDualWeyl
