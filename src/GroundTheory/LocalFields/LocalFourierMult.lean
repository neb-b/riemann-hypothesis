module

public import Mathlib
public import GroundTheory.LocalFields.Different
public import GroundTheory.LocalFields.Bundle0013

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

instance borelSpace_units : BorelSpace Kˣ :=
  measurableEmbedding_units_val.borelSpace isOpenEmbedding_units_val.isInducing



namespace Padic

variable (p : ℕ) [Fact p.Prime] (K) [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

end Padic

end GroundTheory.LocalField
