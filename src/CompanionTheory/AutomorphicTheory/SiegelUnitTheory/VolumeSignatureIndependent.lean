module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.SiegelUnitTheory.UnitsAinf
public import CompanionTheory.AutomorphicTheory.SiegelUnitTheory.ClassNumberMass

@[expose] public section

namespace CompanionTheory.HU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

theorem siegel_mass_rank_one : SiegelOneAll := fun F E _ _ _ _ _ σ h M J hJ => sw1b2 F E σ h M J hJ

theorem mass_ratio_under_volume : ∀ D : D7, RT.MassRatioUnderVolume D := hU_of siegel_mass_rank_one

end CompanionTheory.HU
