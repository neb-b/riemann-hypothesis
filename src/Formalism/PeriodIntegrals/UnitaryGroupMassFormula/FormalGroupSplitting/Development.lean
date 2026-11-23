module

public import Formalism.PeriodIntegrals.Bundle0002

@[expose] public section

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit MvPowerSeries

def S1 : Prop :=
  ∀ (K : Type) [Field K] (l ex : PowerSeries K), PowerSeries.constantCoeff ex = 0 →
    PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧ PowerSeries.subst l ex = PowerSeries.X

theorem coeff_expMv {K : Type} [Field K] {σ : Type} (f : MvPowerSeries σ K) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), coeff α (f ^ n) / (n.factorial : K) := rfl

end PI.FglPhSplit.Wk

end
