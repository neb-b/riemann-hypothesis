module

public import Mathlib
public import Formalism.ThetaSupremumBounds.StatementA
public import Formalism.LogFactorialIndices.Bundle0001

@[expose] public section

open Finset MeasureTheory
open scoped ComplexConjugate Real

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

def liftBlock {Pl ι W : Type} [Fintype Pl] [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (c : (Pl × ι → ℕ) → ℂ) (Rc : (Pl × ι → ℕ) →₀ W) (lam : Pl → ℂ) : W :=
  Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x, lam x.1 ^ e x) • A)

def liftOp {Cl Cl' A B : Type} [Fintype Cl] [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (γ : Cl → ℝ) (ε : Cl → Cl' → ℂ)
    (T : Cl → Cl' → A →L[ℂ] B) (fn : Cl → A) (L' : Cl') : B :=
  ∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)

def liftNormSq {Cl Cl' A B : Type} [Fintype Cl] [Fintype Cl'] [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ)
    (T : Cl → Cl' → A →L[ℂ] B) : ℝ :=
  sInf {X : ℝ | 0 ≤ X ∧ ∀ fn : Cl → A,
    (∑ L', γ' L' * ‖liftOp γ ε T fn L'‖ ^ 2) ≤ X * ∑ L, γ L * ‖fn L‖ ^ 2}

end Formalism.DimensionVariation
