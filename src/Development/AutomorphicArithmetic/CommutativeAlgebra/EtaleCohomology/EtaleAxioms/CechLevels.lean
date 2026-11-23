module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.CechLevels.Cech0Iso
public import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.LevelsGenOfSpecLim
public import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.LevelsOfGen
public import Development.EtaleCohomology.EtaleSheaves.Bundle0052

@[expose] public section

namespace UpperTheory.Et.CechLevelsEtaleAxioms

theorem a0 : LateralTheory.E.LevelsGenPf.SpecLim := LateralTheory.E.SpecLimPf.SpecLim_of
theorem a1 : LateralTheory.E.LevelsPf.LevelsGen := LateralTheory.E.LevelsGenPf.LevelsGen_of_specLim a0
theorem a2 : LateralTheory.E.CechLevelsPf.Levels := LateralTheory.E.LevelsPf.Levels_of_gen a1
theorem a3 : LateralTheory.E.t_E1Cut.CechLevels := LateralTheory.E.CechLevelsPf.CechLevels_of' a2

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.CechLevels := a3

end UpperTheory.Et.CechLevelsEtaleAxioms
