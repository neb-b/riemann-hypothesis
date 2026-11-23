module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec

@[expose] public section

namespace CrystallineSemistableComparison

theorem bock : BocksteinInputFromFormal := fun hF => bock_tw (TwSeq.twSeq hF.et.gen) hF

end CrystallineSemistableComparison
