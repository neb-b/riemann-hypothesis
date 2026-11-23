module

public import Mathlib

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

def logRd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log |(NumberField.discr E : ℝ)| / Module.finrank ℚ E

def extDifferent {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    Ideal (𝓞 L) :=
  Ideal.map (RingOfIntegers.mapRingHom ι) (differentIdeal ℤ (𝓞 E))

def DifferentExtNorm.Statement : Prop :=
  ∀ (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L),
    extDifferent ι ≠ ⊥ ∧
      Real.log (Ideal.absNorm (extDifferent ι) : ℝ) = Module.finrank ℚ L * logRd E

end GroundTheory.Heights₂.Heights.NineStatements
