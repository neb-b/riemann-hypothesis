module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

variable (D : D7) (u : D.what₂.Word)

def TwoTerm (A x : ℝ) : Prop := hsDev D u ≤ A * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + x * (d0 D u : ℝ)

def mfL (L : ℝ) : ℝ := (D.R.m : ℝ) ^ 5 * D.R.f * L

def kfk : ℝ := (D.R.k : ℝ) * D.R.f * Real.log D.R.k

def SDiag (L C : ℝ) : Prop :=
  TwoTerm D u (4 * (Real.exp (C * mfL D L) + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D))

def Small (L C : ℝ) : Prop := (d0 D u : ℝ) ≤ D.what₂.Dstar * Real.exp (-(2 * C * mfL D L))

def eDiag (L C : ℝ) : ℝ := 8 * Real.exp (-(C * mfL D L)) + 6 * Real.exp (-(kfk D / 2))

def RankMu : Prop :=
  (d0 D u : ℝ) = ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def cK : ℝ := (c0 D.s u * c0 D.s u) ^ (-(1 / 2 : ℝ))

namespace Pts

variable (F : Pts)

end Pts

end GlobalTheory.Core.Rk

end
