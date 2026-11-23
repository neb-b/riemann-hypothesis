module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaIndependence.YliftLeOrth
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0034

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scalPairs_betaFree (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalPairs.BetaFree D u u' :=
  PI.UnitaryGroupMassFormula.BetaIndep.betaIndep_of D u u' (beta_mod_iota_surjective D u u')
