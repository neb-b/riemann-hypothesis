module

public import Mathlib
public import Formalism.DoubleCosetMeasures.StatementV
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.Bundle0002
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle0001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0009
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions MeasureTheory Matrix ComplexConjugate

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hkSigPar_lt (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) < DV.sigPar D τ i := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dite_eq_left h1, dite_eq_left h0]
    have a := (D.hc τ).u_gt_v ⟨i + 1, h1⟩
    have b := (D.hc τ).v_gt_u ⟨i, h0⟩
    exact a.trans b
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb, dite_eq_left h0]
      have a := (D.hc τ).u_last_gt (by omega) (by omega)
      have b := (D.hc τ).v_gt_u ⟨i, h0⟩
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      have e2 : (⟨i + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have b' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        rw [← e2]
        exact b
      exact a.trans b'
    · have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb2 : i - (D.R.k - 1) + 1 < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb1, dite_eq_right h0, dite_eq_left hb0]
      have a := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have b := (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ hb2
      have e1 : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, hb2⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  obtain ⟨a, ha⟩ := DV.sigPar_int D τ i
  obtain ⟨b, hb⟩ := DV.sigPar_int D τ (i + 1)
  have h := hkSigPar_lt D τ i hi
  rw [ha, hb] at h
  have h' : b < a := by exact_mod_cast h
  have h'' : (b : ℚ) + 1 ≤ a := by exact_mod_cast h'
  rw [DV.aPlusQ_eq, DV.aPlusQ_eq, ha, hb]
  push_cast
  linarith

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c + 1 < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  have h1 : j + (c + 1) < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dite_eq_left h0, dite_eq_left h1]
  have a := (D.hc τ).gap_be ⟨j + c, h0⟩
  have b := (D.hc τ).gap_eb ⟨j + c, h0⟩ hc
  have e1 : (⟨j + (c + 1), h1⟩ : Fin D.R.m) = ⟨j + c + 1, hc⟩ := by
    rw [Fin.mk.injEq]
    omega
  rw [e1]
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c c' : ℕ) (h : c ≤ c') (hc' : j + c' < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ c' := by
  induction c', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (aMinusQ_step D j τ n (by omega))

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Proved

open Formalism.BasicNotions.TH

end Proved

section Split20

set_option linter.unusedVariables false

open Formalism.BasicNotions Formalism.BasicNotions.TH

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Split20

end Formalism.MainNotions.DIV

end
