module

public import Formalism.Bundle0002

@[expose] public section

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.WT

open Formalism

def L1 {N : ℕ} (χ : DirichletCharacter ℂ N) : ℝ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩; (DirichletCharacter.LFunction χ 1).re

def ell {N : ℕ} (χ : DirichletCharacter ℂ N) : ℝ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩;
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

end Formalism.WT
