module

public import Formalism.Bundle0002

@[expose] public section

open Complex Set

noncomputable section

namespace Formalism


open ArithmeticFunction in
def SchiC {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ n * ((x / n - 1 : ℝ) : ℂ)

def GchiC {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  SchiC χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) * x

def famComb {ι : Type} [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (c : ι → ℂ) (x : ℝ) : ℝ :=
  Gz x - (∑ i, c i * GchiC (χ i) x).re

end Formalism
