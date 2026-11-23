module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.KerReg
section
noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.kerReg :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T → KerReg E k := by
  intro n _ _ μ _ E k val T hM
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hM
  have hmem : ∀ x : Mat n, x ∈ GLs n ↔ IsUnit x := (UpperTheory.RealTr.basic n).2.1
  have hG : ∀ y : G n, (y : Mat n) ∈ GLs n := fun y => (hmem _).2 y.isUnit
  have hfun : (fun y : G n => k (y : Mat n)) = fun y : G n => ∑ i, c i • ks i (y : Mat n) := by
    funext y
    exact hsum _ (hG y)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    refine continuous_finsetSum _ fun i _ => ?_
    have hc : ContinuousOn (ks i) (GLs n) := (hks i).2.1.continuousOn
    exact (hc.comp_continuous Units.continuous_val hG).const_smul (c i)
  · choose R hR using fun i => (hks i).2.2.1
    refine HasCompactSupport.intro (K := {y : G n | lg (y : Mat n) ≤ ∑ i, |R i|})
      (UpperTheory.RealTr.lgCpt n _) ?_
    intro y hy
    simp only [Set.mem_setOf_eq, not_le] at hy
    rw [hsum _ (hG y)]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : R i ≤ ∑ j, |R j| :=
      (le_abs_self (R i)).trans
        (Finset.single_le_sum (f := fun j => |R j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    rw [hR i _ (hG y) (lt_of_le_of_lt hle hy), smul_zero]
  · intro y hy k₁ k₂
    have hu : IsUnit ((k₁ : Mat n) * y * (k₂ : Mat n)) :=
      ((Unitary.toUnits k₁).isUnit.mul ((hmem y).1 hy)).mul (Unitary.toUnits k₂).isUnit
    rw [hsum _ ((hmem _).2 hu), hsum _ hy, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hks i).2.2.2.1 y hy k₁ k₂, mul_smul_comm, smul_mul_assoc]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Rdcalc
section
noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.rdcalc :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V],
      (∀ f f' : Mat n → V, Set.EqOn f f' (GLs n) → ∀ X, Set.EqOn (Rd X f) (Rd X f') (GLs n)) ∧
      ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) → (∀ X, ContDiffOn ℝ ∞ (Rd X f) (GLs n)) ∧
        (∀ X Y, ∀ g ∈ GLs n, Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g) ∧
        ∀ h ∈ GLs n, ∀ X, ∀ g ∈ GLs n, Rd X (fun y => f (h * y)) g = Rd X f (h * g) ∧
          Rd X (fun y => f (y * h)) g = Rd (h⁻¹ * X * h) f (g * h) := by
  intro n V _ _
  refine ⟨fun f f' e X => GlobalTheory.CompanionTheory.RCalc.Rd_congr X e, fun f hf =>
    ⟨fun X => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf, fun X Y g hg => GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y hf hg,
      fun h hh X g hg => ?_⟩⟩
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have hhg : h * g ∈ GLs n := by
    show (h * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hh hg
  have hgh : g * h ∈ GLs n := by
    show (g * h).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  constructor
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hhg
    have hc : HasFDerivAt (fun y : Mat n => f (h * y))
        ((fderiv ℝ f (h * g)).comp (GlobalTheory.CompanionTheory.RCalc.mulL h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => h * y) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulL h).hasFDerivAt
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulL_apply, mul_assoc]
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hgh
    have hc : HasFDerivAt (fun y : Mat n => f (y * h))
        ((fderiv ℝ f (g * h)).comp (GlobalTheory.CompanionTheory.RCalc.mulR h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => y * h) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulR h).hasFDerivAt
    have e : g * h * (h⁻¹ * X * h) = g * X * h := by
      rw [Matrix.mul_assoc g h, ← Matrix.mul_assoc h, ← Matrix.mul_assoc h, Matrix.mul_nonsing_inv h hdet,
        Matrix.one_mul, Matrix.mul_assoc]
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulR_apply, e]
end
end

