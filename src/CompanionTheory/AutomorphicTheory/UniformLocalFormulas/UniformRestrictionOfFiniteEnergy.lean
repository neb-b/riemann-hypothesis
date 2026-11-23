module

public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfEnergy
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Bundle0001
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.RankOneTermInvariant

@[expose] public section

namespace Formalism.MainStatements.RowRest

theorem uniqOfPin : UniqOfPin := fun _ _ _ _ C hB u u' νl hP => use₇ C hB u u' νl hP

theorem uniform_restriction_of_finite_energy (hE : EnergyFin) : Formalism.L2.SG.Pf.ThmBChain6.AmplitudeBoundsAllChoicesUniform :=
  uniform_restriction_of_energy covariance_formula uniqOfPin hE

end Formalism.MainStatements.RowRest
