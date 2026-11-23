module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.PInsertNth

@[expose] public section

namespace PositivityTheory.KB

theorem sStokes_of : SStokes := by
  intro V _ _ U hU hUc q ω hω y hy
  exact StokesSlices.asm StokesSlices.subAlt StokesSlices.subHyp StokesSlices.subSlice U hU hUc q ω hω y hy

end PositivityTheory.KB
