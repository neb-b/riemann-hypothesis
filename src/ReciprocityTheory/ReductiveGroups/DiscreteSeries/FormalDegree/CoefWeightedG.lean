module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0013
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

theorem coefWeightedN {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hlam : Formalism.QuantumDeterminants.IsHCParam lam)
    (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (w : H) (hw : Formalism.MainNotions.S.IsLowUnit ε lam σ w) (h : ℝ)
    (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (N : ℝ) (hN : 0 ≤ N)
    (hthr : 1 ≤ S7.q0 ε → (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h ∧
      8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) * (N + 2 * (n : ℝ) * S7.q0 ε) < h)
    (μ : Measure (Formalism.REAL.UJ ε)) [hμ : μ.IsHaarMeasure] :
    ∫⁻ g, ‖⟪w, σ (Formalism.MainNotions.S.uMat g) w⟫_ℂ‖ₑ *
        ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Formalism.MainNotions.S.uMat g)‖ ^ N) ∂μ < ⊤ := by
  haveI : CompleteSpace H := hDS.1
  obtain ⟨hcont, hle⟩ := coef_continuousOn_le_one hDS hw
  have hH : Measure.IsHaarMeasure (μ : Measure (S7.UJ ε)) := hμ
  have hI : Integrable (fun g : S7.UJ ε =>
      ‖⟪w, σ (S7.toM g) w⟫_ℂ‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N) μ := by
    rcases Nat.eq_zero_or_pos (S7.q0 ε) with hq | hq
    · exact @integrable_opPow_of_compact _ _ hq _ hcont hle _ hN μ hH
    · have hq1 : 1 ≤ S7.q0 ε := hq
      obtain ⟨hstd, h8'⟩ := hthr hq1
      have hq1r : (1 : ℝ) ≤ S7.q0 ε := by exact_mod_cast hq1
      have hs1 : 1 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by linarith)
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hq0 : (0 : ℝ) ≤ S7.q0 ε := by positivity
      have hP0 : 0 ≤ N + 2 * (n : ℝ) * S7.q0 ε := by positivity
      have hP : N + 2 * (n : ℝ) * S7.q0 ε ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) * (N + 2 * (n : ℝ) * S7.q0 ε) :=
        le_mul_of_one_le_left hP0 hs1
      have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
        nlinarith [mul_nonneg hn0 hq0]
      exact @integrable_opPow_of_dec _ _ _ hcont hle _ hq1
        (fun k X hX => coef_dec_of_isDS hDS hlam hgap hq1 h8 hstd hw k hX) _ hN h8' μ hH
  refine lt_of_le_of_lt (le_of_eq ?_) hI.hasFiniteIntegral
  refine lintegral_congr fun g => ?_
  have hpos : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Formalism.MainNotions.S.uMat g)‖ ^ N :=
    Real.rpow_nonneg (norm_nonneg _) N
  show _ = ‖‖⟪w, σ (Formalism.MainNotions.S.uMat g) w⟫_ℂ‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Formalism.MainNotions.S.uMat g)‖ ^ N‖ₑ
  rw [Real.eNorm_eq_ofReal (mul_nonneg (norm_nonneg _) hpos), ENNReal.ofReal_mul (norm_nonneg _),
    ofReal_norm]

end ReciprocityTheory.ChartRestriction.DS
