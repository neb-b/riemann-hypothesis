module

public import Formalism.WindowSums.AnnihilatorPolynomials.Bundle0001
public import Formalism.WindowSums.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
public import Formalism.WachModuleLifts.StatementW

@[expose] public section

namespace Formalism.WindowSums

theorem arc_ZpowVal : ZpowVal := valuation_zpow_sub_one
theorem arc_ValProd : ValProd := valProd_of valuation_zpow_sub_one
theorem arc_KillerVal : KillerVal := killerVal_of valuation_zpow_sub_one
theorem arc_KillerKills : KillerKills := annihilatorPoly_kills
theorem arc_WindowSum : WindowSum := sum_padicValInt_le
theorem arc_Lagrange : Lagrange := lagrange_annihilation

end Formalism.WindowSums
