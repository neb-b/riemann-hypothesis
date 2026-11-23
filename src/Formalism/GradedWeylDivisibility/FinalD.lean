module

public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0013
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLDiag
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem sSIdxFinite : SSIdxFinite := semistandard_index_finite
theorem sSBasis : SSBasis := semistandard_basis
theorem rowActDiagWeight : RowActDiagWeight := row_action_diagonal_weight
theorem rowActMul : RowActMul := row_action_mul
theorem nablaLLe : NablaLLe := nabla_weight_le
theorem nablaLBasis : NablaLBasis := nablaLBasis_of rowActMul
theorem nablaLKBasis : NablaLKBasis := nablaLKBasis_of rowActMul sSBasis
theorem nablaLDiag : NablaLDiag := nablaLDiag_of rowActMul rowActDiagWeight nablaLBasis
theorem nablaLTwMem : NablaLTwMem := nabla_twist_mem
theorem tensorBasis : TensorBasis := tensor_power_basis
theorem blockActTensor : BlockActTensor := block_action_tensor

end Formalism.GradedWeylDivisibility
