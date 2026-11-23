module

public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt

@[expose] public section

noncomputable section

namespace Formalism.CohomologicalDescent.Down

section SLD

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD

section SLD2

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD2

section SF06

open CategoryTheory CategoryTheory.Limits
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

end SF06

section SF07

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative

end SF07

section SF09

open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

def InclWReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.JW P l) ∧ X.Jmin l ≤ W.JW P l

end SF09

end Formalism.CohomologicalDescent.Down
