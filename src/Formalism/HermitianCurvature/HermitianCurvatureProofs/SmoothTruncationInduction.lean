module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0251
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0261

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem smooth_truncation_induction : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ _ _ hγ hΩ t ht e Fc hFc hag
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_induction Wp Wq P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag

theorem smooth_truncation_exists : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF _ t ht e
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_exists_formula Wp Wq P p F j hj w h hh hF t ht e

end Formalism.FourierDecayAlt.P
