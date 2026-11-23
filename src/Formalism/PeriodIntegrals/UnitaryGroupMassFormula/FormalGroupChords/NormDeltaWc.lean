module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014

@[expose] public section

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

theorem isWq_bridge {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h : IsWq W wq) : PI.AddIntG.IsWq W wq := h

end PI.FglChordFactor.Wk
