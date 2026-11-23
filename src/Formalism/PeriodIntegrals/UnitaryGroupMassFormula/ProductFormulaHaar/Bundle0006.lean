module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.SumLocalTrace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Assemble
section
namespace PI.ProdFormulaE.Assemble

theorem prodFormulaE_of_haar (hH : St.HaarAlg) : PI.ProdFormulaE.ProdFormulaE :=
  Top.prodFormulaE_of hH modulus_eq_finitePlace Tr.sumLocalTrace TrIntP.norm_trace_le_one ResCharP.eq_iff_mem_asIdeal

end PI.ProdFormulaE.Assemble
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarAlg
section
namespace PI.ProdFormulaE.HaarAlgP

theorem haarScaling : St.HaarAlg := by
  refine haarAlg_of ?_ ?_
  · intro K _ _ _ _ E _ _ _ _ _ _ n b μ _ i a ha
    exact PI.ProdFormulaE.HaarBox.scale_box b μ i a ha
  · intro K _ _ _ _ E _ _ _ _ n b t
    exact PI.ProdFormulaE.HaarBox.transvection_box b t

end PI.ProdFormulaE.HaarAlgP
end

