module

public import Mathlib
public import GroundTheory.PAdicHodge.BCrisNewton
public import GroundTheory.PAdicHodge.Bundle0007
public import GroundTheory.PAdicHodge.CyclotomicTower

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

section Frob

variable [FiniteDimensional ℚ_[p] K]

end Frob

section Valuation

variable {K}

theorem exists_norm_eq_zpow_maxUnramified {x : maxUnramified p K} (hx : x ≠ 0) :
    ∃ D : ℤ, ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D :=
  (isACrisFraction_of_mem (mem_maxUnramified.1 x.2).2).exists_norm_eq_zpow
    (fun h => hx (Subtype.ext h))

theorem norm_p_algCl_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)



end Valuation

section FrobValuation

variable [FiniteDimensional ℚ_[p] K]

end FrobValuation

end ACris

end GroundTheory.PAdicHodge
