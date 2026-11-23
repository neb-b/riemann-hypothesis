module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocalDepthTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalLocalDepthTwo.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B],
    SerreSAt B 2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalOpenMapping
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def NormalOpenMapping.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
    ∃ O : Set (σ → ℂ), IsOpen O ∧ φ '' U = zeroSetIn I ∩ O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametrisationSheetsConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ParametrisationSheetsConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
    IsLocalParametrisation X w B A D δ N → GermIrreducibleAt X w →
      IsPreconnected {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyDerivationsDetectSquare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def PolyDerivationsDetectSquare.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime]
    (g : MvPolynomial (Fin n) k), g ∈ p →
      (∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) →
        algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
          maximalIdeal (Localization.AtPrime p) ^ 2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermNullstellensatz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable def holGermIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (f : Fin k → (σ → ℂ) → ℂ) : Ideal (holGerms w) :=
  Ideal.span {φ | ∃ i, (φ : Germ (𝓝 w) ℂ) = (f i : Germ (𝓝 w) ℂ)}

def PrimeGermNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → AnalyticAt ℂ g w → (holGermIdeal w p).IsPrime →
    (∀ᶠ z in 𝓝 w, (∀ i, p i z = 0) → g z = 0) →
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, g z = ∑ i, h i z * p i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def RegularLocusDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
    ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧
      ∀ B : Set (σ → ℂ), IsOpen B → B ⊆ N → X ∩ B ⊆ closure (regLocus (X ∩ B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def RegularOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)), I.IsPrime →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧
      ∀ z ∈ zeroSetIn I, eval z h ≠ 0 → IsRegularPointOf (zeroSetIn I) z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularQuotientIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def RegularQuotientIndependent.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsRegularLocalRing S] (h : ℕ) (x : Fin h → S),
    (∀ i, x i ∈ maximalIdeal S) →
    (∀ a : Fin h → S, ∑ i, a i * x i ∈ maximalIdeal S ^ 2 → ∀ i, a i ∈ maximalIdeal S) →
      IsRegularLocalRing (S ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreCriterion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreCriterion.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → (NormalRing A ↔ SerreR A 1 ∧ SerreS A 2)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreRFlatAscent.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsNoetherianRing A → IsNoetherianRing B →
    Module.Flat A B → ∀ k : ℕ, SerreR A k →
      (∀ (P : Ideal B) [P.IsPrime], SerreRAt (primeFibreLocalRing A P) k) → SerreR B k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreSFlatAscent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreSFlatAscent.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsNoetherianRing A → IsNoetherianRing B →
    Module.Flat A B → ∀ k : ℕ, SerreS A k →
      (∀ (P : Ideal B) [P.IsPrime], SerreSAt (primeFibreLocalRing A P) k) → SerreS B k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetPieceProductAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def SheetPieceProductAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ)
    (U V : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ),
    IsLocalParametrisation X w B A D δ N → IsOpen U → IsOpen V →
    {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V → {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅ →
    ∃ f : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ f (A ⁻¹' D) ∧
      ∀ z, A z ∈ D → δ (A z) ≠ 0 →
        f z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = A z}, (ℓ z - ℓ x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

