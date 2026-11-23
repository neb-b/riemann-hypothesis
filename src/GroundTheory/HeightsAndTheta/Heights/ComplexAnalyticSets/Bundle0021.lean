module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularSequence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

def FlatLocalRegularSequence.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ∀ (rs : List A) (ys : List B), (∀ r ∈ rs, r ∈ maximalIdeal A) → IsWeaklyRegular A rs →
        (∀ y ∈ ys, y ∈ maximalIdeal B) →
        IsWeaklyRegular (B ⧸ (maximalIdeal A).map (algebraMap A B))
          (ys.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))) →
        IsWeaklyRegular B (rs.map (algebraMap A B) ++ ys)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibresRegular.Statement : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A], Algebra.FiniteType k A →
    ∀ (m : Ideal A), m.IsMaximal → ∀ (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing A P)

noncomputable def polyOriginIdeal : Ideal (MvPolynomial (Fin 1) ℂ) :=
  RingHom.ker (MvPolynomial.eval (0 : Fin 1 → ℂ))

theorem polyOriginIdeal_isMaximal : polyOriginIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun z => ⟨MvPolynomial.C z, by simp⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermFiniteProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def GermFiniteProjection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
      (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) ∧
      ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermMinimalPolynomialDivides
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def GermMinimalPolynomialDivides.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ) = 0) ∧
        ∀ E : Polynomial ((Fin d → ℂ) → ℂ), (∀ k, AnalyticAt ℂ (E.coeff k) (A w)) →
          (∀ᶠ z in 𝓝 w, z ∈ X → E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (g z) = 0) →
          ∀ᶠ y in 𝓝 (A w),
            (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ) ∣
              E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImageDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ImageDimLe.Statement : Prop :=
  ∀ (n m : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ), P.IsPrime →
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleFiniteGermProjectionOpenAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleFiniteGermProjectionOpenAt.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∀ V ∈ 𝓝 x, A '' (X ∩ V) ∈ 𝓝 (A x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IrreducibleGermComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (h : (σ → ℂ) → ℂ),
    IsAnalyticNear X w → GermIrreducibleAt X w → AnalyticAt ℂ h w →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ X → h z = 0) →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsPreconnected ((X ∩ B) \ {z | h z = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

def IrreducibleGermCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ),
    IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) X

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermMeetOverHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IrreducibleGermMeetOverHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y Z : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W ∈ 𝓝 w, ∀ x ∈ Y ∩ W, A x = A w → x = w) →
    IsAnalyticNear Z w → (¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) →
    ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z → e (A z) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionImageNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermProjectionImageNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ x ∈ X ∩ N₀, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) →
      (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionOpenNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermProjectionOpenNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ x ∈ X ∩ N₀, ∀ V ∈ 𝓝 x, A '' (X ∩ V) ∈ 𝓝 (A x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsolatedFibreNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∃ N₀ ∈ 𝓝 w, ∀ x ∈ X ∩ N₀, ∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

