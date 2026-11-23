module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def FrameGraphGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (q : MvPolynomial (Fin n) ℂ), I₀.card = d ∧ q ∉ J ∧
        ∀ z ∈ zeroSetEuc J, eval (fun i => z i) q ≠ 0 →
          ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
            (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
              DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
              zeroSetEuc J ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameJacobianGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def frameDeriv {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (j : Fin n)
    (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ l, C (b j l) * pderiv l f

def frameJacobianDet {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  Matrix.det (Matrix.of fun k j : {j // j ∉ I} => frameDeriv b j (f k))

def FrameJacobianGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ),
        I₀.card = d ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ frameJacobianDet b I₀ f ∉ J ∧
          ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFramePlaneGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def FramePlaneGraph.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (J' : Ideal (MvPolynomial (Fin n) ℂ)), I₀.card = d ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') < d ∧
        ∀ z ∈ zeroSetEuc J \ zeroSetEuc J', ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
          (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
            DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
            (zeroSetEuc J \ zeroSetEuc J') ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights
end

