module

public import Formalism.HyperbolicPlaceProducts.Bundle0001
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.Bundle0001
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SesquilinearDeterminantHolds
public import Mathlib
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CountO

@[expose] public section

namespace Formalism.SLP.Final

theorem torsionIndex : Formalism.SLP.TorsionIndex := Formalism.SLP.P.card_range_nsmul_mul_card_le
theorem sesqDet : Formalism.SLP.SesqDet := Formalism.SLP.P.sesquilinear_determinant_holds
theorem omegaPow : Formalism.SLP.OmegaPow := Formalism.SLP.P.pow_primeFactors_length_le
theorem submoduleIndexCountO : Formalism.SLP.SubmoduleIndexCountO := Formalism.SLP.P.card_submodules_of_index_le
theorem submoduleCountDed : Formalism.SLP.SubmoduleCountDed := Formalism.SLP.P.card_submodules_le_of_dedekind

end Formalism.SLP.Final
