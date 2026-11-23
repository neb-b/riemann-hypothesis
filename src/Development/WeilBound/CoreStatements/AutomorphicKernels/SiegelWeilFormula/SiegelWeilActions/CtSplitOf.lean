module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0011
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0008
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PsiTContPer
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SecUnfOfCLaw

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Act

theorem ctSplit_of : AuxiliaryPrimeFunction → CoefEx → CTSplit := fun _ _ =>
  ctSplit_of_parts indepDom cptDom absConv firstEq (secLaw_of (secUnf_of absConv))

end PositivityTheory.SiegelWeilFormula.Act

end
