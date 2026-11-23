module

public import Mathlib
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.LogFactorialIndices.Bundle0001
public import Formalism.ThetaSupremumBounds.StatementE

@[expose] public section

open Finset
open scoped Real

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

def liftedMapLogSize {J Pl Emb : Type} [Fintype Pl] {r : ℕ} (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' : J → ℝ) (v : ℝ)
    (j : J) (s : Emb) : ℝ :=
  (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j))

end Formalism.DimensionVariation
