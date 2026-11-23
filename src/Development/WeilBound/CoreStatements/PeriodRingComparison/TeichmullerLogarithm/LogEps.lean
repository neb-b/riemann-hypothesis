module

public import Mathlib
public import Development.WeilBound.CoreStatements.PeriodRingComparison.TeichmullerLogarithm.ZeroEquivLogTerm
public import Development.WeilBound.CoreStatements.PeriodRingComparison.PrimitiveEpsilon.UntiltEpsilonEqOne

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem acris_log_teichmuller_epsilon : cA l (Reformulated.AutPerF.Acris.logTeich (eps0 l)) = Formalism.Per6.tA l :=
  cA_logTeich_eps l (untilt_epsilon_eq_one l)

end Cmp6
