module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe

@[expose] public section

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace

namespace PositivityTheory.Rg.Tf.Core

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def PolyBd (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ (φ : L2 μ) (x : G1 K n), ‖rconv (Gam K n) μ a φ x‖ ≤ C * qht x ^ N * ‖φ‖

def CuspDecay (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) : Prop :=
  ∀ N' : ℕ, ∃ C : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ x : G1 K n,
    ‖rconv (Gam K n) μ a φ x‖ ≤ C * (qht x ^ N')⁻¹ * ‖φ‖

end PositivityTheory.Rg.Tf.Core
