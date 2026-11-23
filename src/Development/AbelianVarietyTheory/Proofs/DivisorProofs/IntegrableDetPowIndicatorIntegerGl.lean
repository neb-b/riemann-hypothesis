module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.GJTransfer

theorem integrable_indicator_intM_mul_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ : ℝ), (n : ℝ) - 1 < σ →
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  intro k _ _ _ _ _ _ n σ hσ
  have hint : ∀ (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), -1 < s →
      ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
        (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
    intro μ _ s hs
    exact _root_.GlobalTheory.GJInt.intdet k μ n s hs
  exact integrable_haarVol_of_lintegral n σ (min (σ - n) 0) (min_le_left _ _)
    (hint _ _ (lt_min (by linarith) (by norm_num)))

end GlobalTheory.GJTransfer
