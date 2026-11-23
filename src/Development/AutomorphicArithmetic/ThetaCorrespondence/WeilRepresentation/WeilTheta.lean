module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds

@[expose] public section

namespace UpperTheory.Lit

theorem siegelSetUnitary_of_core : GlobalTheory.Published.SiegelSetUnitary := PositivityTheory.ThKR.siegel_of_core PositivityTheory.Prw.siegelCore_holds

theorem weilThetaConvergence : GlobalTheory.Published.WeilThetaConvergence :=
  GlobalTheory.WeilThetaConv.weilThetaConvergence_of_siegelSet siegelSetUnitary_of_core

end UpperTheory.Lit
