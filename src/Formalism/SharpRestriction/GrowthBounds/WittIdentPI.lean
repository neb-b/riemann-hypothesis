module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.Bundle0001

@[expose] public section

namespace Formalism.MainNotions.G.WittPI

theorem wittIdent_of (H : PI.WittUnram) : Formalism.MainNotions.G.WittIdent :=
  fun p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS =>
    H p n' W Qq σ hS.frac_alt hS.p_unif hS.res_card hS.eq_sum_herm_smul_frame_of_inW hS.frob

theorem wittIdentity_holds : Formalism.MainNotions.G.WittIdent := wittIdent_of witt_unramified

end Formalism.MainNotions.G.WittPI
