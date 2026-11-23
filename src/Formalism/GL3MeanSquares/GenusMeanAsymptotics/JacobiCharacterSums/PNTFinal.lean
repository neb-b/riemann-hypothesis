module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTSharp
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0021
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSum
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0029
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0031
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSumL

@[expose] public section

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem explicitS_proof' : ExplicitS := smoothed_explicit_formula

theorem logDensityM_proof' : LogDensityM := Dens.log_density_bound

theorem deuringHeilbronnMB_proof' : DeuringHeilbronnMB := deuring_heilbronn_lossy

theorem pnt_progressions_relative_weak_holds : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW :=
  prime_count_of_psi (glue_ranges psi_relative_near_range
    (psi_relative_far_range explicitS_proof' differenced_explicit_formula (zero_sum_bound_lossy logDensityM_proof' deuringHeilbronnMB_proof')))

end Formalism.HermitianLattices.Ext.PrimesInProgressions
