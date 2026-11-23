module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.StepTransl

@[expose] public section

noncomputable section

namespace PI.FT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}

variable {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
  {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}

end Lin

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
variable (R : Type) [CommRing R] [Algebra F R]

end Tens

end PI.FT
