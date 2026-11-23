module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.HatCap
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.HatKBSOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0286

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

open Formalism.FourierDecayAlt.P.CutMP

theorem normal_form_hat_product_bessel : NFHatProdKBS := by
  refine ⟨1, 18, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p e L he hQ hL N u hN hu
  exact hatProdJB hat_product_bound polynomial_decay_admissible P p.T.base p.hP p.hl.2.2 e L he hQ hL N u hN hu

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
