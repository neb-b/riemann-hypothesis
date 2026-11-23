module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.FirstMinimumPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0001

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

def mono {n : ℕ} {ι Y : Type*} (s : Fin n → ι → Y → ℂ) (α : Fin n → ℕ) (j : ι) (y : Y) : ℂ :=
  ∏ k, s k j y ^ α k

end

end ReciprocityTheory.ChartRestriction.G.AR
