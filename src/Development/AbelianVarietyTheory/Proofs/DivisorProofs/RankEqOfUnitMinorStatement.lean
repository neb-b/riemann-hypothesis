module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankEqOfUnitMinor
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal

@[expose] public section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_eq_of_unit_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  first | exact @GlobalTheory.unitMinorSet_rank_eq | exact GlobalTheory.unitMinorSet_rank_eq | (intros; apply GlobalTheory.unitMinorSet_rank_eq <;> assumption)
