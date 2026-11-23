module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.ReductionTauOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0004

@[expose] public section

set_option autoImplicit false

namespace Formalism.L2.SG.Pf.Tau

theorem reduction_theory_of_lattice (h0 : LatticeCommensurable) (h8 : MinkowskiSubmodule) : ReductionTau :=
  reductionTau_of (third_estimate_of_first_two h0 (lattice_finitelyGenerated_of_commensurable h0)) (sizes_locally_comparable t4 t5) t7 h8 (lattice_vectors_bounded_below h0) (packet_conditions_closed (lattice_finitelyGenerated_of_commensurable h0) t2)

theorem reductionTau_of_minkowskiSubmodule (h8 : MinkowskiSubmodule) : ReductionTau :=
  reduction_theory_of_lattice t0 h8

end Formalism.L2.SG.Pf.Tau
