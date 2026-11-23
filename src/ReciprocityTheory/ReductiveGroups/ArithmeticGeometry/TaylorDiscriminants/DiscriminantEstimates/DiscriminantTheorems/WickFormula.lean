module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.LprodAddSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenVan

@[expose] public section

theorem wick_formula : PI.WickFormula :=
  PI.WickFormula.wickFormula_of PI.WickFormula.ordLin_holds PI.WickFormula.ordX_holds
    PI.WickFormula.base_holds PI.WickFormula.bComm_holds PI.WickFormula.Gen.powXL_holds
    PI.WickFormula.Gen.commL_holds PI.WickFormula.Gen.vanL_holds
