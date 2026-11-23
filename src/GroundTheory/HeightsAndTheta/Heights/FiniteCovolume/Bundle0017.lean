module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0011

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHaarParabolicCoordinates
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def HaarParabolicCoordinates.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (x₀ : W), x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ (ν : Measure (vecFixGroup h v x₀)) (κ : Measure M.stab)
      (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧ Measurable τ ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ f : archUnitary h v → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = ∫⁻ b : InfinitePlace E → ℂ, (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
          ∫⁻ k : M.stab, ∫⁻ x : vecFixGroup h v x₀, f (x * (τ b * k)) ∂ν ∂κ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHyperbolicPairs
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Transitive

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def HyperbolicPairTransitive.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v w v' w' : W, IsHyperbolicPair h v w → IsHyperbolicPair h v' w' →
    ∃ g : h.unitaryGroup, g • v = v' ∧ g • w = w'

end Transitive

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineIndex
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

noncomputable section

def LineIndexNeZero.Statement (E W : Type*) [Field E] [NumberField E] [AddCommGroup W] [Module E W] :
    Prop :=
  ∀ (La : AddSubgroup W) (x : W), IsLattice E La → x ∈ La → x ≠ 0 → lineIndex E La x ≠ 0

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def MajorantStabCompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ M : Majorant h v, IsCompact (M.stab : Set (archUnitary h v))

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerCovolume
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def StabilizerCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∀ (ν : Measure (vecFixGroup h v x₀)), ν.IsHaarMeasure →
    ∃ FD₀ : Set (vecFixGroup h v x₀),
      IsFundamentalDomain ((vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀)) FD₀ ν ∧
      0 < ν FD₀ ∧ ν FD₀ < ⊤

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

