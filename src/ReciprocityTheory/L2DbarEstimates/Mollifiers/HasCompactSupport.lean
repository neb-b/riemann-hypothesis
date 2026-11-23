module

public import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

theorem Kernel.hasCompactSupport (K : Kernel E μ) : HasCompactSupport K.toFun :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun x hx => by
    by_contra h
    exact hx (ball_subset_closedBall (K.support_subset h))

end

theorem moll_smooth (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothSt E μ := fun K _ hu =>
  K.hasCompactSupport.contDiff_convolution_left _ K.smooth hu

theorem moll_support (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SupportSt E μ := by
  intro K u
  refine (support_convolution_subset _).trans ?_
  rw [add_comm]
  exact Set.add_subset_add_left K.support_subset

theorem kernel_std (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : StdSt E μ := by
  have h : (fun ε : ℝ => (Kernel.std E μ ε).r) =ᶠ[𝓝[>] 0] id := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [Kernel.std, Kernel.ofBump, stdBump, show (0 : ℝ) < ε from hε]
  exact (tendsto_congr' h).2 (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)

end ReciprocityTheory.L2DbarEstimates.B
