module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm

open Formalism.BasicNotions Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n n' : ℕ}

theorem fockF_eq_fockS {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = fockS f f := by
  unfold Formalism.REAL.fockF fockS mfact
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem fockS_self_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : ∃ r : ℝ, 0 ≤ r ∧ fockS f f = r := by
  refine ⟨∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ), by positivity, ?_⟩
  unfold fockS
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Complex.conj_mul']
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm
