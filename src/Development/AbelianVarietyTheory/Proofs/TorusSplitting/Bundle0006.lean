module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExtAllInputs
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CharStatementHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.GCauchyHolds
section
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaTorus

theorem gSup_holds : GSupStatement := gSup GlobalTheory.packingCount

theorem propA_holds : PropAStatement := propA GlobalTheory.packingCount GlobalTheory.gaussTail_of_card_le

theorem dim_holds : DimStatement := dim

theorem J_holds : JStatement :=
  jOf GlobalTheory.ext_all_inputs _root_.GlobalTheory.greedy_splitting_exists GlobalTheory.charStatement_holds
    (colTorus GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colAbel GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colEmpty GlobalTheory.ext_all_inputs propA_holds gSup_holds)

theorem N_holds : NStatement := lemmaN dim_holds

theorem I_holds : IStatement := iOf J_holds N_holds

end GlobalTheory.ThetaTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaBound
section
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem theta_bound_tStatement : TStatement :=
  tOf ext_all_inputs _root_.GlobalTheory.greedy_splitting_exists (gSup ext_all_inputs.1) dim

end GlobalTheory
end

