module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdPre
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntEqFour

@[expose] public section

open GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem siegelWeilStd_of_ct (hCT : CTSplit) : SiegelWeilStd := siegelWeilStd_pre TW.Twp.poisson hCT

end PositivityTheory.SiegelWeilFormula.Fin
