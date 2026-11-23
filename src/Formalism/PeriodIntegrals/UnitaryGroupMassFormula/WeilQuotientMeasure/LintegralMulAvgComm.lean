module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat

@[expose] public section

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace PI.WeilQuotMeas.UnitaryGroupMassFormula

section Lemmas

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}

theorem measurable_mul_coe : Measurable (fun p : G × H => p.1 * (p.2 : G)) := measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)

theorem measurable_avg (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := (hf.comp measurable_mul_coe).lintegral_prod_right'

theorem avg_mul_right (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (k : H) :
    ∫⁻ h, f (g * (k : G) * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have e := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using e

end Lemmas

end PI.WeilQuotMeas.UnitaryGroupMassFormula
