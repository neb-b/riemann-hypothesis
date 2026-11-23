module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpenPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def IsolatedFibreOpenPoly.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) → x ∈ zeroSet P →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x) →
    ∀ W' ∈ 𝓝 x, (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ W') ∈
      𝓝 (fun i => eval x (p i))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def isolatedFibrePts {n m : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (z : Fin m → ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ (∀ i, eval x (Q i) = z i) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, (∀ i, eval x' (Q i) = z i) → x' = x}

def IsolatedPointsCount.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts J Q z).encard ≤ N

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearNoetherNormalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearNoetherNormalization.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalBranchedCovering
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalBranchedCovering.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ)),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (W : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (δ : (Fin k → ℂ) → ℂ),
      IsOpen W ∧ w ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = A w → z = w) ∧
      (∀ z ∈ zeroSetIn I ∩ closure W, A z ∈ D → z ∈ W) ∧
      DifferentiableOn ℂ δ D ∧
      (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, δ t ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ zeroSetIn I ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ zeroSetIn I ∩ W, A z = y' → z ∈ Set.range (fun j => s j y')) ∧
      ∀ z ∈ zeroSetIn I ∩ W, ∀ ε > 0, A '' (zeroSetIn I ∩ Metric.ball z ε) ∈ 𝓝 (A z)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalTrace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalTrace.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w → HolomorphicOnSubset g (zeroSetIn I ∩ U) →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (T : (Fin k → ℂ) → ℂ),
      IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ B, A z = A w → z = w) ∧ DifferentiableOn ℂ T D ∧
      ∀ y ∈ D, ∃ x : Fin m → σ → ℂ, (∀ j, x j ∈ zeroSetIn I ∩ B ∧ A (x j) = y) ∧
        (∀ z ∈ zeroSetIn I ∩ B, A z = y → z ∈ Set.range x) ∧ T y = ∑ j, g (x j)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalUniversalDenominator
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalUniversalDenominator.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (U : Set (σ → ℂ)) (f : (σ → ℂ) → ℂ),
    I.IsPrime → h ∉ I → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ g : MvPolynomial σ ℂ, g ∉ I ∧ ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧ N ⊆ U ∧
      ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F N ∧
        ∀ z ∈ (zeroSetIn I ∩ N) \ {z | eval z h = 0}, eval z g * f z = F z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaximalCountUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def MaximalCountUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    ∀ x ∈ Y, {x' | x' ∈ Y ∧ A x' = A x}.encard = N →
      ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalBoundedQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalBoundedQuotient.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    Bornology.IsBounded ((fun z => F z / G z) '' ((zeroSetIn I ∩ N) \ {z | G z = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧
      IsPreconnected ((zeroSetIn I ∩ B) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIntegrallyClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalGermIntegrallyClosed.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ) (d : ℕ) (a : Fin d → (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N → (∀ j, DifferentiableOn ℂ (a j) N) →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    (∀ z ∈ (zeroSetIn I ∩ N) \ {z | G z = 0},
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) = 0) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIrreducible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalGermIrreducible.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      GermIrreducibleAt (zeroSetIn I) w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocallyIrreducible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalLocallyIrreducible.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧
      IsPreconnected ((zeroSetIn I ∩ B) \ {z | eval z h = 0}) ∧
      zeroSetIn I ∩ B ⊆ closure ((zeroSetIn I ∩ B) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

