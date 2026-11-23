module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

@[expose] public section

noncomputable section

open PositivityTheory.RgJS

namespace UpperTheory.V.Z.Tf.GOne


open Classical in
def ExtId : Prop := by
  classical
  exact ForSys fun q X _ A => ∀ x y : X, ∃ F : ℂ → ℂ, (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ) ∧
    ∀ σ : ℝ, 1 < σ → F σ = (if x = y then (σ : ℂ) - 1 else 1) * Complex.exp (∑' p, lterm q (A x) (A y) σ p)

def LogTwo : Prop := ForSys fun q X _ A => ∀ x : X, ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
  |(∑' p, lterm q (A x) (A x) σ p).re + Real.log (σ - 1)| ≤ C

def CrossUp : Prop := ForSys fun q X _ A => ∀ x y : X, x ≠ y → ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
  (∑' p, lterm q (A x) (A y) σ p).re ≤ C

def PartCS : Prop := ForSys fun q X _ A => ∀ (x y : X) (I : Set _) (σ : ℝ), 1 < σ →
  ‖∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A y) σ p.1‖ ^ 2 ≤
    (∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re * (∑' p, lterm q (A y) (A y) σ p).re

end UpperTheory.V.Z.Tf.GOne

end
