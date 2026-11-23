module

public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WeightedBoundRotatedUniformOfCubicThreshold
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveInputsOfHypothesesGlobal
public import CompanionTheory.AutomorphicTheory.RankOneTori.FrameBesselBoundOfLargeConstants

@[expose] public section

namespace CompanionTheory.WaveGrid

theorem weighted_bound_rotated_uniform_of_hypsG (H : BranchingSupport.HypsG) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  uniform_bessel_rank_three_of_inputs (WEnd.wave_inputs_of_hypotheses_global H) fun D => Formalism.MainStatements.RankOne.one_bessel_torus_bound D (le_refl 100)

end CompanionTheory.WaveGrid
