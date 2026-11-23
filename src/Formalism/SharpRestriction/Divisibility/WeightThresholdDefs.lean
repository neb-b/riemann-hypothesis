module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.WeightThresholdDefs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Classical

def dE (D : D7) : ℕ := (NumberField.discr D.host.E).natAbs

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev dimY : ℕ := dimFl D.what₂.Tau Y.N

def gap (lam : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) : ℝ :=
  lam τ ⟨Y.j - 1, by have := Y.j_lt; omega⟩ - lam τ ⟨Y.j, Y.j_lt⟩

def supAbs (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := ⨆ x : Rt D.what₂.Tau Y.N, |lam x.1 x.2|

def bigB0 (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 * (1 + supAbs Y u / g)

end Derived

def cP (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

variable {D : D7} (V : DivX D) (P : DIV.Align.PrinLev V)

def TrivialFlagIntersectionCond : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (V.shv S κ).arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) *
      (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

structure Loc4 where

  dRho : V.Surf → ℕ
  dRho_pos : ∀ t, 0 < dRho t

  CHr : V.Surf → Type
  instCHr : ∀ t, AddCommGroup (CHr t)

  ch2 : ∀ t, CHr t

  ch2o : ∀ t, CHr t

  arithFirstChernHom : ∀ t, ℝ →+ CHr t

  degA : ∀ t, CHr t →+ ℝ

attribute [instance] Loc4.instCHr

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

end Fam

end Formalism.MainNotions.WeightThresholdDefs

end
