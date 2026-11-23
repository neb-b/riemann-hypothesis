module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim

@[expose] public section

theorem nablaDim_closed : PI.NablaDim := fun n nu h => Formalism.L2.G.Model.weyl_dualWeyl ℂ n nu h

theorem modelIso_closed : PI.ModelIso := modelIso_of polynomial_coefficients unitaryGroupDense_holds highest_weight_irreducible

theorem weylForU_closed : PI.WeylForU := weylForU_of modelIso_closed nablaDim_closed
