module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Forward
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0024

@[expose] public section

namespace PI.StabPairsW

theorem gram_matrix_invariance : GramInv := gramInv_of frameInd

theorem stabilizer_pair_formula : PairFormula := pairFormula_of gram_matrix_invariance

theorem stabPairs_of_converse (h : ConverseStep) : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  stabPairs_of mapsStep stabilizer_pair_formula h compDet

end PI.StabPairsW
