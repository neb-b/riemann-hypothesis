module

public import Formalism.GaussJetBounds.Bundle0001

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def frameTop {d N0 N1 : ℕ} (TT : Finset (ZMod d)) (y : ZV d N0 N1) : Bool :=
  decide (y.1 ∈ TT ∧ y.2.1.val = 0)

end Formalism.DworkPowerSeriesWeights
