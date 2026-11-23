module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001

@[expose] public section

open KStar.TotallyRealRoots

namespace KStar.IdealValuations

variable (l : ℕ) [Fact l.Prime]

def IsResTrivial (g : Gal(PadicAlgCl l/ℚ_[l])) : Prop :=
  ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1


variable {l} in
noncomputable def complField {E : Type*} [Field E] (j : E →+* PadicAlgCl l) :
    IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range j)

end KStar.IdealValuations
