module

public import Mathlib
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

section Point

variable {D : D7}

def FixedAt (L : SizeData₂ D) : Prop :=
  L.Ct = 401 ∧
  L.j0 = ⌈Real.logb 5 ((D.R.n : ℝ) * (D.R.N D.R.m : ℝ) / (D.R.m : ℝ))⌉₊ ∧
  D.host.Lw = 10 * ⌈(L.Ct + 4) * Real.log L.sc.x⌉₊ + 2 * ⌈30 / L.sc.eps⌉₊ + 22 ∧
  D.host.ccK = ⊤ ∧
  ∀ τ τ' : D.what₂.Tau, (D.hc τ).v = (D.hc τ').v

def RankWindowAt (L : SizeData₂ D) : Prop :=
  (L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) ∧ 4 ≤ D.R.n) ∧
  ((L.sc.x * L.sc.delta1) ^ (1 / 2 : ℝ) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ 2 * (L.sc.x * L.sc.delta1) ^ (1 / 2 : ℝ)) ∧
  (L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ (D.R.k : ℝ) ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps))

def CoarseWindowAt (L : SizeData₂ D) : Prop :=
  L.sc.x ^ (1 / 2 - L.sc.eps / 8) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (1 / 2 : ℝ) ∧ 44 ≤ D.R.m ∧
  L.sc.x ^ (2 + 8 * L.sc.eps) / 2 ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) ∧
  (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps)

def TypePrimeWindowAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧
    (D.R.r : ℝ) ^ 4 * (LevelStarExponents.condE D : ℝ) ^ C ≤ Y ^ (1 / 4 : ℝ) ∧ 2 * Y ≤ L.sc.b ^ 9 ∧
    ∀ i : Fin 2, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y

def BelowCutAt (L : SizeData₂ D) : Prop :=
  (D.host.q : ℝ) < L.sc.X' ∧ (D.host.d : ℝ) < L.sc.X' ∧ (D.host.pde : ℝ) < L.sc.X' ∧ (D.host.pde' : ℝ) < L.sc.X' ∧
  L.sc.X' ≤ L.sc.X'' D.R.n ∧ 2 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) + 1 < L.sc.X'

def WindowsAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  RankWindowAt L ∧ CoarseWindowAt L ∧ TypePrimeWindowAt L C ∧ BelowCutAt L

def hWidth (L : SizeData₂ D) : ℝ := L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1

def lJ (L : SizeData₂ D) : ℝ :=
  (D.R.m : ℝ) * L.sc.b * L.sc.x ^ L.sc.eps / ((D.R.k : ℝ) * ((D.R.m : ℝ) + (D.R.t : ℝ)) * Real.log (3 * hWidth L))

end Point

section Family

variable {eps : ℝ}

end Family

theorem lJ_den_pos {D : D7} (L : SizeData₂ D) :
    0 < (D.R.k : ℝ) * ((D.R.m : ℝ) + (D.R.t : ℝ)) * Real.log (3 * hWidth L) := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  push_cast at hk
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hb : 0 < L.sc.b := Real.exp_pos _
  have h1 : 1 < 3 * hWidth L := by
    unfold hWidth
    have := L.Sc_pos
    have := L.etaSz_pos
    linarith
  exact mul_pos (mul_pos (by linarith) (by linarith)) (Real.log_pos h1)

end GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

end
