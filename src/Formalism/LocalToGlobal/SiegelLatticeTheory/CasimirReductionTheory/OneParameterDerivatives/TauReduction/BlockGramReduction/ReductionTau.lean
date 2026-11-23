module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ReductionTheoryOfLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MinkowskiSubmoduleShortVector
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0003

@[expose] public section

set_option autoImplicit false

namespace Formalism.L2.SG.Pf.Tau

theorem reductionTau : ReductionTau :=
  reductionTau_of_minkowskiSubmodule (minkowski_submodule_short_vector (lattice_finitelyGenerated_of_commensurable t0) t2 t8m)

end Formalism.L2.SG.Pf.Tau
