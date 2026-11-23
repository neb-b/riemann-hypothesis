module

public import Mathlib

@[expose] public section

open Finset

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def nl (kf κs c t : ℝ) : ℝ := kf * c + κs * (2 * c + 1 + t)

def mE (l n : ℕ) : ℕ :=
  if l = 2 then 2 + padicValNat 2 n else if (l - 1) ∣ n then 1 + padicValNat l n else 0

def MinVal : Prop :=
  ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n →
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ padicValNat l (a ^ n - 1) = mE l n

def CESum : Prop :=
  ∀ (f X : ℕ) (S : Finset ℕ), 16 ≤ X → 2 * f ≤ X → (∀ l ∈ S, l.Prime) →
    ∑ l ∈ S, ((f * padicValNat l 2 + mE l X : ℕ) : ℝ) * Real.log l ≤ X * Real.log (X + 1)

end Formalism.PairingDivisionLocalBalance
