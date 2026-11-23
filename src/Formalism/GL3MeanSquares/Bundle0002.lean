module

public import Mathlib
public import Formalism.LogVandermondeBounds.Bundle0002
public import Formalism.GL3MeanSquares.Bundle0001

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.FourierTransformKernelSurjective
section
namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset Matrix

def LemmaB'_avg : Prop :=
  ∀ (k n : ℕ) (S : Finset (Fin k → ℕ)) (mult : (Fin k → ℕ) → ℕ),
    (∀ σ : Equiv.Perm (Fin k), ∀ w ∈ S, w ∘ σ ∈ S) →
    (∀ σ : Equiv.Perm (Fin k), ∀ w, mult (w ∘ σ) = mult w) →
    (∀ w ∈ S, ∑ i, w i = n) →
    ∀ j : Fin k, k * ∑ w ∈ S, mult w * w j = n * ∑ w ∈ S, mult w

end Formalism.HermitianLattices.LocalLatticeBases
end

-- bundled from Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
section
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

noncomputable section

namespace Formalism.HermitianLattices.GL2a2

open Formalism.HermitianLattices.GL2PrimeSums

def LogDerivSeries : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (-(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)))

def PsiZeroConst : Prop :=
  Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR (fun n => Λ n) u - u) / u ^ 2) atTop
    (𝓝 (-1 - Real.eulerMascheroniConstant))

end Formalism.HermitianLattices.GL2a2
end
end

