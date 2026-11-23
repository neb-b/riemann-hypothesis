module

public import Formalism.HermitianCurvature.StatementJF

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

noncomputable section

namespace CompanionTheory.JfS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NN (k r : ℕ) : ℕ := 2 * (2 * r + k + 1) * (2 * r * (2 * r + k + 1) + 1)

section flat

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

end flat

end CompanionTheory.JfS
