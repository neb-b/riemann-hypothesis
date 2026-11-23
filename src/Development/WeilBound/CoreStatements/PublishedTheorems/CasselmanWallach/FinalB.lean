module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CwOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EtaleCohomologyNegativeVanishingDegreeZero

@[expose] public section

namespace PositivityTheory.CWB

theorem casselmanWallach : GlobalTheory.Published.CasselmanWallach :=
  PositivityTheory.CW.cw_of maxPr

end PositivityTheory.CWB
