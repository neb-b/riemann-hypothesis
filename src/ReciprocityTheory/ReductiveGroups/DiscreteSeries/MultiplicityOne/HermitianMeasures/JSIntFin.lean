module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.SharpIntegralGNOfStructuralFacts

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0

theorem sIntFin (h : UnitaryGroupStructuralFacts) : SIntFin :=
  A.sIntFin_of (haarUniqueSF h) (A.closed_unitary_of_hypotheses h) (A.compact_unitary_of_hypotheses h) (A.exists_haar_W_of_structural_facts h) (A.closedN_of_structural_facts h)
    (A.haar_exists_nilpotent_of_hypotheses h) (A.norm_lower_bound_of_hypotheses h)
    (A.nIntAt_all (A.nilpotent_basis_of_hypotheses h) (A.nRecHaar_of_structural_facts h) (A.haar_unique_of_hypotheses h) (A.closedN_of_structural_facts h) (A.haar_exists_nilpotent_of_hypotheses h)
      (A.norm_lower_bound_of_hypotheses h))

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0
