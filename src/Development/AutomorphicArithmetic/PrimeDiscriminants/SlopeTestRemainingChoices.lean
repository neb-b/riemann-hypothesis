module

public import Mathlib
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition

@[expose] public section

noncomputable section

namespace Formalism.HC

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

def vdH (p : ℕ) : ℝ := (padicValNat p (NumberField.discr H.E).natAbs : ℝ) / (Module.finrank ℚ H.E : ℝ)

theorem vdH_nonneg (p : ℕ) : 0 ≤ H.vdH p := by unfold vdH; positivity

end HostRaw

end Formalism.HC

end
