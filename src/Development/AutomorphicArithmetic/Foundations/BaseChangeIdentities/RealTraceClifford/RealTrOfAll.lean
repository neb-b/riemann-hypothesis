module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace UpperTheory.RealTr

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev UK (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

section U

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U))

def coef (w v : U) : Mat n → ℂ := fun g => ⟪w, piM π g v⟫_ℂ

def IsOpK [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (B : ((E.V →L[ℂ] ℂ) →L[ℂ] U) →ₗ[ℂ] ((E.V →L[ℂ] ℂ) →L[ℂ] U)) : Prop :=
  ∀ t ξ, B t ξ = ∫ y : G n, π y (t (ξ ∘L k y.val)) ∂μ

end U

def KerReg (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  Continuous (fun y : G n => k y.val) ∧ HasCompactSupport (fun y : G n => k y.val) ∧
    ∀ y ∈ GLs n, ∀ k₁ k₂ : UK n, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def e1 (D : Mat n →ₗ[ℝ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) - Complex.I • D (Matrix.single a b Complex.I))

def e2 (D : Mat n →ₗ[ℝ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  -((1 / 2 : ℂ) • (D (Matrix.single b a 1) + Complex.I • D (Matrix.single b a Complex.I)))

end Alg

end UpperTheory.RealTr
