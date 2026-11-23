module

public import Mathlib

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism


open ArithmeticFunction in
def LamF {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ :=
  Λ n * (1 + (χ n).re)

def S {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LamF χ n * (x / n - 1)

def gammaF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  Real.eulerMascheroniConstant +
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

def G {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  S χ x - x * Real.log x + (1 + gammaF χ) * x

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def quadraticCharFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def quadraticCharThree : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

def quadraticCharacterMod7 : DirichletCharacter ℂ 7 := (quadraticChar (ZMod 7)).ringHomComp (Int.castRingHom ℂ)

end Formalism
