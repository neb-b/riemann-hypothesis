module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeUnimodular
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0023

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.NormMMOfJD
section
namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem normMM_of_JD (hE : JordanExists) (hD : DetLocal) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_NM (nMPseudo_of hE hD count_extension norm_mass_assembly)

theorem normMM_of_J (hE : JordanExists) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_JD hE determinant_local

end PI.UnitaryGroupMassFormula.CntFormula.R6
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowSurjOfGenus
section
namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem rowSurj_of_genus (hJ : UnimodOneGenus) : RowSurj :=
  rowSurj_of hJ partner_vector_exists lattice_integral lamUnimod lattice_flag_exists local_genus_exists

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end

