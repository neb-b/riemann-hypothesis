module

public import Mathlib
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

@[expose] public section

theorem Formalism.HC.HostRaw.vdH_le_natAbs {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) :
    H.vdH p ≤ ((NumberField.discr H.E).natAbs : ℝ) := by
  unfold Formalism.HC.HostRaw.vdH
  have h1 : (1 : ℝ) ≤ (Module.finrank ℚ H.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have h2 : padicValNat p (NumberField.discr H.E).natAbs ≤ (NumberField.discr H.E).natAbs :=
    Nat.padicValNat_def ▸ Nat.multiplicity_le_self _
  have h3 : (padicValNat p (NumberField.discr H.E).natAbs : ℝ) ≤ ((NumberField.discr H.E).natAbs : ℝ) := by exact_mod_cast h2
  exact (div_le_self (Nat.cast_nonneg _) h1).trans h3
