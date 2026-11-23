module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictValC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivClosedOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.HighestWeightVectorUnique

@[expose] public section

namespace Formalism.L2.SG.Pf

theorem valuation_character_irreducible : ColDictPf.ValCIrr :=
  ColDictValCPf.valCIrr_of ColDictValCPf.transfer_holds
    (ColDictValCPf.divisor_closed_holds ColDictValCPf.density_holds)
    ColDictValCPf.high_existence_holds ColDictValCPf.highest_weight_vector_unique ColDictValCPf.generation_holds

end Formalism.L2.SG.Pf
