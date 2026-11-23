module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0006

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Automorphic Matrix

instance fact_gaussQ : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩

abbrev GaussQ : Type := QuadraticAlgebra ℚ (-1) 0

instance : Algebra.IsQuadraticExtension ℚ GaussQ :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

end GroundTheory.Heights₂.Theta
