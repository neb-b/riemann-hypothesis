module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StCriticalFibreInfinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def CriticalFibreInfinite.Statement : Prop :=
  ∀ (k d : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin d → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
      (∀ t ∈ U, ¬ Function.Injective (fderiv ℂ f t)) →
        ∃ y : Fin d → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCovolumeRelIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory

def CovolumeRelIndex.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁]
    [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂], L₁ ≤ L₂ →
      ZLattice.covolume L₁ μ = (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsEmbeddingSumPlaces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace

def EmbeddingSumPlaces.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : (F →+* ℂ) → ℝ),
    (∀ σ, g (ComplexEmbedding.conjugate σ) = g σ) →
      ∑ σ : F →+* ℂ, g σ = ∑ w : InfinitePlace F, (mult w : ℝ) * g w.embedding

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeCountVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

def LatticeCountVolume.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La]
    [IsZLattice ℝ La] (S T : Set E), MeasurableSet S → (∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) →
      μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume La μ)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMixedBoxCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding


open scoped Classical in
def MixedBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F)) [DiscreteTopology La]
    [IsZLattice ℝ (E := mixedSpace F) La] (f : InfinitePlace F → ℝ), (∀ w, 0 < f w) →
      {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite ∧
        Real.log (convexBodyLTFactor F : ℝ) + ∑ w, (mult w : ℝ) * Real.log (f w) -
            Module.finrank ℚ F * Real.log 2 - Real.log (ZLattice.covolume La) ≤
          Real.log ({y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.ncard : ℝ)

end GroundTheory.Heights₂.Heights.Targets
end

