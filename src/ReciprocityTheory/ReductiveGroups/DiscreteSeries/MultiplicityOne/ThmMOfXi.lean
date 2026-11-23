module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TheoremMOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeHerm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0013
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UuInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRankOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem thmM_of_xi (h : UnitaryGroupStructuralFacts) (hXi : Formalism.FourierDecayAlt.B.XiExists) : ThmM :=
  theoremM_of h hXi (stBeHerm h) (stBePos h) (stSchurW h) (stSInt h) stSchurG (stPairs h) (stBeConv h) (stBeEquiv h)
    (stRepro h) (stSmooth h) stFrame (stInvGroup h) stInvChar stInvCC (stReps h) (stTransM h) (stSym h) (stSymBeta h)
    (stBetaInf h) (stDichoG h) (stDichoW h) (stMixed h) rankOneMinors

theorem thmM : ThmM := thmM_of_xi multiplicity_one_hypotheses_hold ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end ReciprocityTheory.ChartRestriction.DS.Mult1
