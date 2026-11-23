module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IndependentSectionsUpperCount
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TaylorExpansionLocalCoordinates
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0010
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR

open MeasureTheory Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La)

theorem mem_multiIndicesBelow_iff {a0 : ℕ} {α : Fin n → ℕ} : α ∈ multiLt n a0 ↔ ∑ k, α k < a0 := by
  simp [multiLt, Finset.Nat.mem_antidiagonalTuple]

end

end ReciprocityTheory.ChartRestriction.G.AR
