module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHomogDimZeroPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

def HomogDimZeroPow.Statement : Prop :=
  ∀ (n : ℕ) (K : Ideal (MvPolynomial (Fin n) ℂ)),
    K.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) ≤ 0 → ∃ N : ℕ, originIdeal n ^ N ≤ K

theorem originIdeal_eq_ker (n : ℕ) :
    originIdeal n = RingHom.ker (constantCoeff : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  ext f
  rw [originIdeal, ← Set.image_univ, mem_ideal_span_X_image, RingHom.mem_ker, constantCoeff_eq]
  constructor
  · intro h
    by_contra h0
    obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.2 h0)
    exact hi rfl
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact mem_support_iff.1 hm h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
    exact ⟨i, Set.mem_univ _, hi⟩

theorem originIdeal_isMaximal (n : ℕ) : (originIdeal n).IsMaximal := by
  rw [originIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C _ _⟩)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPointsOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermPointsOffDiscriminant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A x) ∧ (¬ ∀ᶠ y in 𝓝 (A x), δ y = 0) ∧
      ∀ W ∈ 𝓝 x, ∀ᶠ y in 𝓝 (A x), δ y ≠ 0 → ∃ x' ∈ X ∩ W, A x' = y

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermPrimitiveForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∃ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A x)) ∧ AnalyticAt ℂ δ (A x) ∧ (∀ i j, AnalyticAt ℂ (q i j) (A x)) ∧
      (¬ ∀ᶠ y in 𝓝 (A x), δ y = 0) ∧
      (∀ᶠ z in 𝓝 x, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (∀ᶠ y in 𝓝 (A x), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      ∀ i, ∀ᶠ z in 𝓝 x, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermRegularConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsPreconnected (regLocus (X ∩ B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermRegularDimGe.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N ∈ 𝓝 w, ∀ x ∈ X ∩ N, ∀ (e : ℕ) (A' : (σ → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ))
      (V : Set (σ → ℂ)) (g : (Fin e → ℂ) → σ → ℂ),
      IsOpen O → IsOpen V → x ∈ V → AnalyticOnNhd ℂ g O → (∀ y ∈ O, A' (g y) = y) → X ∩ V = g '' O →
        d ≤ e

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCountPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def IsolatedPointsCountPrime.Statement : Prop :=
  ∀ (n m : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)), P.IsPrime → ∀ (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianPrimeDerivations
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def JacobianPrimeDerivations.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)), p.IsPrime →
    ∃ (h : ℕ) (f : Fin h → MvPolynomial (Fin n) k)
      (D : Fin h → Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))
      (s : MvPolynomial (Fin n) k),
      (∀ i, f i ∈ p) ∧ s ∉ p ∧ (∀ x ∈ p, s * x ∈ Ideal.span (Set.range f)) ∧
        (Matrix.of fun i j => D j (f i)).det ∉ p

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLeadIdealDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LeadIdealDim.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ leadIdeal J) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearFormCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.Statement : Prop :=
  ∀ (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ∃ B : Matrix (Fin 1) (Fin n) ℂ,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (I ⊔ linIdeal B)) ≤ (e : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def LocalGraphMass.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))), I₀.card = d →
    (∀ z ∈ S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω) →
    ∀ R : ℝ, μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R) ≤
      ∑ I ∈ Finset.univ.powersetCard d,
        (⨆ x : I → ℂ, frameFibreCount b I S x) *
          μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalParametrisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def LocalParametrisation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w →
    ∀ U ∈ 𝓝 w, ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ))
      (δ : (Fin d → ℂ) → ℂ) (N : ℕ), B ⊆ U ∧ IsLocalParametrisation X w B A D δ N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ManifoldZerosComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (R : Set (σ → ℂ)) (h : (σ → ℂ) → ℂ),
    IsPreconnected R → (∀ x ∈ R, IsRegularPointOf R x) → (∀ x ∈ R, AnalyticAt ℂ h x) →
    (∃ x ∈ R, h x ≠ 0) → IsPreconnected (R \ {z | h z = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

