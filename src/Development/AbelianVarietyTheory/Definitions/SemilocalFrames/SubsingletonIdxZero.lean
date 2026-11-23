module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def sgnCN (k r : ℕ) : Fin (2 * r + k + 1) → Bool := fun i =>
  if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

structure HRep (k r : ℕ) where
  H : Type
  [nG : NormedAddCommGroup H]
  [iP : InnerProductSpace ℂ H]
  σ : Mat k r → (H →L[ℂ] H)

attribute [instance] HRep.nG HRep.iP

variable {k r : ℕ}

namespace Ex

open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Ex

end GlobalTheory.Mom
