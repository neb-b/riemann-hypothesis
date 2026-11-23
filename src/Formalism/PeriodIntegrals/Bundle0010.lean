module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.ZerosWindow
section
noncomputable section

namespace PI

def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def ZerosWindowWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))

def ZerosWindow : Prop := ∃ C : ℝ, 0 < C ∧ ZerosWindowWith C

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.ZerosWindowIn
section
namespace PI

def LBoundRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 0 < s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re)

def ZetaBoundRight : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)

def LInvRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖DirichletCharacter.LFunction χ s‖⁻¹ ≤ s.re / (s.re - 1)

end PI
end

