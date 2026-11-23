module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.NeronOggShafarevich
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.Bundle0002

@[expose] public section

namespace UpperTheory.Lit

theorem neronOggShafarevich : GlobalTheory.Published.NeronOggShafarevichSt := UpperTheory.Lit.Nos.Nos.neronOggShafarevich

theorem potentialGoodReduction : GlobalTheory.Published.PotentialGoodReductionSt :=
  GlobalTheory.potentialGoodReduction_of_neronOggShafarevich neronOggShafarevich

theorem cmPotentialGoodReduction : GlobalTheory.Published.CMPotentialGoodReductionSt :=
  cmPotentialGoodReduction_of_nos neronOggShafarevich

theorem serreTateGoodReduction : GlobalTheory.Published.SerreTateGoodReductionSt :=
  ⟨neronOggShafarevich, potentialGoodReduction, cmPotentialGoodReduction⟩

end UpperTheory.Lit
