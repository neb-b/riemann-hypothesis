module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.RealPlaceAnalysis.Bundle0004

@[expose] public section

open Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.TypeHW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem prod_Icc (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => f (j + 1)) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

end CompanionTheory.D.Inhab.TypeHW
