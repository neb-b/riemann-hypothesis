module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0016
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0019
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0013
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OsOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.AStepSuccOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0018

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem xiExists_of_in (h : InductiveHeisenbergInputs) : Formalism.FourierDecayAlt.B.XiExists :=
  xiExists_of_induction_steps (aStepBase_of h (tBothH iwB h))
    (aStepSucc_of h iwB (tLeftH iwB h) FormulaFAux.formulaF_all (ch_of c1))
    (bStepBase_of h)
    (bStepSucc_of h iwB FormulaFAux.formulaF_all
      (oscillatoryBound' (tailFin_of (ch_of c1)) c1 quadraticSublevelDecay' ker slow))
    (coefStep_of h (tBothH iwB h) (det_of h)) (xiIntH h)

theorem xiExists : Formalism.FourierDecayAlt.B.XiExists := xiExists_of_in heisenbergHaarFacts_hold

end ReciprocityTheory.ChartRestriction.DS.Xi
