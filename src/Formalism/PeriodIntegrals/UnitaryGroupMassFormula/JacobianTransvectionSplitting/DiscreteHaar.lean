module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW


open Classical in
def modF (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] (a : F) : ℝ≥0∞ := by
  classical
  exact if h : a = 0 then 0 else ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞)

def LinModulus : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (M : Matrix ι ι F), M.det ≠ 0 →
    ∀ ν : Measure (ι → F), ν.IsAddHaarMeasure → ∀ S : Set (ι → F), MeasurableSet S →
      ν ((fun x => M *ᵥ x) '' S) = modF F M.det * ν S

def LinModulusV : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F]
    (V : Type) [AddCommGroup V] [Module F V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι], Nonempty (V ≃L[F] (ι → F)) →
    ∀ f : V →ₗ[F] V, LinearMap.det f ≠ 0 →
    ∀ ν : Measure V, ν.IsAddHaarMeasure → ∀ S : Set V, MeasurableSet S →
      ν (f '' S) = modF F (LinearMap.det f) * ν S

def DiagOne : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (i : ι) (a : F), a ≠ 0 →
    ∀ ν : Measure (ι → F), ν.IsAddHaarMeasure → ∀ S : Set (ι → F), MeasurableSet S →
      ν ((fun x => Function.update x i (a * x i)) '' S) = modF F a * ν S

end PI.NglqJacSplitW
