module

public import Formalism.LocalRingCardinality.HostCls

@[expose] public section

open Formalism.HC

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R) {p : ℕ}

theorem cls_splitK_or_small (hp : p.Prime) (h : p ≤ H.splitBound) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    H.cls p = .splitK ∨ p ∈ H.small := by
  by_cases hs : p ∈ H.small
  · exact Or.inr hs
  · have h2 : p ≠ 2 := fun e => hs (e ▸ H.two_mem_small)
    exact Or.inl ((primeClass_eq_splitK_iff H.toHostRaw).2 ⟨hs, hq, hd, H.split_small p hp h2 h⟩)

end Formalism.BasicNotions.Host
