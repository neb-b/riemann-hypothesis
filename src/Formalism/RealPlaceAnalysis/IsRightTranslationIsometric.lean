module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.REAL

structure HidaSetting (n : ℕ) (ε : Fin n → Bool) where
  E : Type
  [ng : NormedAddCommGroup E]
  [ips : InnerProductSpace ℂ E]
  [cs : CompleteSpace E]
  S : Subgroup (UJ ε)
  σ : S → E →ₗᵢ[ℂ] E
  ν : Measure (UJ ε)

attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs

def Rs {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h : UJ ε) (F : UJ ε → E) : UJ ε → E :=
  fun g => F (g * h)

end Formalism.REAL
