module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.InFrameInvOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.KAway

theorem awayAct_of_tAll (hT : PositivityTheory.SiegelWeilFormula.TAll) : PositivityTheory.SiegelWeilFormula.AwayAct :=
  awayAct_of hT PositivityTheory.SiegelWeilFormula.kfour.auxEx adDecomp

theorem finAct_of_tAll (hT : PositivityTheory.SiegelWeilFormula.TAll) : PositivityTheory.SiegelWeilFormula.FinAct :=
  finAct_of hT PositivityTheory.SiegelWeilFormula.kfour.auxEx adDecomp

end PositivityTheory.SiegelWeilFormula.KAway
