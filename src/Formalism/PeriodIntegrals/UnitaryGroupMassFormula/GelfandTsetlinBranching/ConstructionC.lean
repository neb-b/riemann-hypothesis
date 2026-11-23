module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.Bundle0003

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem realize_of (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) : Realize := by
  intro n N hN lam mu f hf hfix hne
  subst hN
  exact realize_C h he ha n lam mu f hf hfix hne

end PI.WGB
