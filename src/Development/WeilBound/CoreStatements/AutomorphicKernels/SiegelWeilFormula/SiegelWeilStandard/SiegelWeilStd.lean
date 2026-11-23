module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOfCt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOf

@[expose] public section

open GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem siegelWeilStd : SiegelWeilStd := siegelWeilStd_of_ct (Act.ctSplit_of kfour.auxEx kfour.coefEx)

end PositivityTheory.SiegelWeilFormula.Fin
