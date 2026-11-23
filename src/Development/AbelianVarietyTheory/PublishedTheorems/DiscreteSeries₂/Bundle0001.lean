module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.DSExist
section
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def DSExist : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam mu →
    (∃ P, PI.UpqRep.IsCayleyU k r ε P) → ∃ R : Rep k r, R.IsDS ε mu

end BranchingSupport
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
section
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def IsInvForm {k r : ℕ} (R R' : Rep k r) (Bf : R.H → R'.H → ℂ) : Prop :=
  (∀ x ∈ R.sm, ∀ x' ∈ R.sm, ∀ y ∈ R'.sm, Bf (x + x') y = Bf x y + Bf x' y) ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (a • x) y = a * Bf x y) ∧
  (∀ x ∈ R.sm, ∀ y ∈ R'.sm, ∀ y' ∈ R'.sm, Bf x (y + y') = Bf x y + Bf x y') ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x (a • y) = star a * Bf x y) ∧
  (∀ g ∈ GG k r, ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (R.σ g x) (R'.σ g y) = Bf x y) ∧
  ∃ (C : ℝ) (Ws Ws' : List (List (Mx k r))), (∀ W ∈ Ws ++ Ws', ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
    ∀ x ∈ R.sm, ∀ y ∈ R'.sm, ‖Bf x y‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W x‖).sum *
      (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W y‖).sum

def Poulsen : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r),
    R.IsDS ε mu → R'.IsDS ε mu' →
    (∀ Bf : R.H → R.H → ℂ, IsInvForm R R Bf → ∃ c : ℂ, ∀ x ∈ R.sm, ∀ y ∈ R.sm, Bf x y = c * ⟪y, x⟫_ℂ) ∧
    ∀ Bf : R.H → R'.H → ℂ, IsInvForm R R' Bf → (∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)

end BranchingSupport
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Zuckerman
section
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def Zuckerman : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu →
    (∀ a c, a < c → 2 ≤ mu a - mu c) →
    (∀ (l : ℕ) (RI : Sub (2 * r + k + 1) l → Rep k r), (∀ I, (RI I).IsDS ε (addSet mu I.1)) →
      ∃ io pr, TensRaw (cmp l) R RI io pr) ∧
    (∀ RI : Fin (2 * r + k + 1) → Rep k r, (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) →
      ∃ io pr, TensRaw dualM R RI io pr)

end BranchingSupport
end
end

