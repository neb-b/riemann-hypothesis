module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.S.Pv.PeriodG

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.BesselSplit

variable {k r : ℕ}

section Period

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]

end Period

section Period2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]

end Period2

theorem thrStar_le {n : ℕ} (ε : Fin n → Bool) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε ≤ (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2 + 16 * (n : ℝ) + 8 := by
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hp : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by
    have : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
      unfold ReciprocityTheory.ChartRestriction.DS.pOf
      exact (Finset.card_le_univ _).trans (Fintype.card_fin n).le
    exact_mod_cast this
  have hq : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by
    have : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
      unfold ReciprocityTheory.ChartRestriction.DS.qOf
      exact (Finset.card_le_univ _).trans (Fintype.card_fin n).le
    exact_mod_cast this
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ n := by
    have h0 : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := min_le_left _ _
    have h0' : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by exact_mod_cast h0
    linarith
  have hq00 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := Nat.cast_nonneg _
  have hs : √(2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ n + 1 := by
    calc √(2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ √(((n : ℝ) + 1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = n + 1 := Real.sqrt_sq (by linarith)
  have hpq : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n * n :=
    mul_le_mul hp hq (Nat.cast_nonneg _) hn
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left hpq hn]
  · nlinarith [mul_le_mul_of_nonneg_left hq0 hn]

theorem exponent_ok (k r : ℕ) {h : ℝ} (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (ε : Fin (2 * r + k + 1) → Bool) :
    ∃ m : ℕ, Formalism.FourierDecayAlt.ThreeDimData.AG k r < m ∧ ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h := by
  obtain ⟨hk, hh, -, -⟩ := hok
  refine ⟨⌊Formalism.FourierDecayAlt.ThreeDimData.AG k r⌋₊ + 1, ?_, ?_⟩
  · push_cast
    exact Nat.lt_floor_add_one _
  · have h1 := thrStar_le ε
    have hAGv : Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k : ℝ) + r) * (r + 1) := rfl
    have hAG : (0 : ℝ) ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
      rw [hAGv]
      positivity
    have hfl : (⌊Formalism.FourierDecayAlt.ThreeDimData.AG k r⌋₊ : ℝ) ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := Nat.floor_le hAG
    push_cast at hh h1 ⊢
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hr : (0 : ℝ) ≤ r := r.cast_nonneg
    set x : ℝ := 2 * (r : ℝ) + k + 1 with hx
    have hx2 : 2 ≤ x := by linarith
    have hkr : ((k : ℝ) + r) * (r + 1) ≤ x * x :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hAGle : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (x * x) := by
      rw [hAGv]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ x * x),
      mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ x)]

end Formalism.L2.S.Pv.PeriodG
