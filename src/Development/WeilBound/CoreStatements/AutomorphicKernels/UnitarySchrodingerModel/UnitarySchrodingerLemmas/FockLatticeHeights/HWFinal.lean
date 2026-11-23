module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HeightWNOfFin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.BlockMulVec.BotVBlk4MulVec

@[expose] public section

namespace PositivityTheory.PfSWUS.SwFockk

theorem heightWN : PositivityTheory.PfSWUS.SwMatch.HeightWN :=
  heightWN_of_fin PositivityTheory.PfSWUS.SwsHwfin.hwFin

end PositivityTheory.PfSWUS.SwFockk
