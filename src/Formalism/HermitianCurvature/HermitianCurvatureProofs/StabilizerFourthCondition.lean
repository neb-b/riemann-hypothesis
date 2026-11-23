module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem determinant_nonzero : C2.DetNonzero := by
  intro k r z z' hz hz' g hG hdet
  have hD : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have h1 : Complex.normSq (Dmin k r z z' g (Fin.last (r + 1))) = 0 := by
    rw [hD, hdet, map_zero]
  unfold Gf at hG
  rw [h1] at hG
  have h2 := mul_nonneg (mul_nonneg hz.2.le hz'.2.le)
    (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))
  linarith

end Formalism.FourierDecayAlt.P
