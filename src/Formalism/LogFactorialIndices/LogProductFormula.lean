module

public import Formalism.LogFactorialIndices.SignedSubspaceIndex.Bundle0001
public import Mathlib
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet

@[expose] public section

namespace Formalism.LatticeIndexTer

theorem latFinite : LatFinite := lattice_quotient_finite
theorem latBasis : LatBasis := lattice_has_basis
theorem idxDet : IdxDet := lattice_index_eq_det_valuation

end Formalism.LatticeIndexTer
