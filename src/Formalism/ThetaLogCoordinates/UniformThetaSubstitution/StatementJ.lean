module

public import Mathlib
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0002
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0001

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

def thetaLog {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K)
    (ϖ : K) (μ : PowerSeries K) (Tht : MvPowerSeries (Bool × EV ν r0 r1) K) :
    MvPowerSeries (ZV ν r0 r1) K :=
  MvPowerSeries.subst
    (fun x => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K))
    (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x) Tht)

end Formalism.InvariantFactorPaths.G7
