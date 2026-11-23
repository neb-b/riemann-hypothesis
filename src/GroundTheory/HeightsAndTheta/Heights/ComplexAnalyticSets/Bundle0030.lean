module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCotangentBasisInPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def CotangentBasisInPrime.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime],
    ∃ (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) ∧
      maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 ∧
      ∀ a : Fin h → Localization.AtPrime P,
        ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
          ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationAdicCompletion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def DerivationAdicCompletion.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Derivation ℤ R R),
    ∃ D' : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      ∀ r : R, D' (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) (D r)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationCotangentIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def DerivationCotangentIndependent.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (D : Fin h → Derivation ℤ T T)
    (f : Fin h → T), (∀ i, f i ∈ P) → (Matrix.of fun i j => D j (f i)).det ∉ P →
      ∀ a : Fin h → Localization.AtPrime P,
        ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈
            maximalIdeal (Localization.AtPrime P) ^ 2 →
          ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteGermProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)),
      IsOpen B → B ⊆ N₀ → w ∈ X ∩ B → IsOpen D → IsPreconnected D → Set.MapsTo A (X ∩ B) D →
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
      (∀ x ∈ X ∩ B, A x = A w → x = w) →
      ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ), IsLocalParametrisation X w B A D δ N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloGeneralEquation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def FiniteModuloGeneralEquation.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] [DecidableEq τ] (x : σ → ℂ) (k : ℕ)
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (c : τ),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    (∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : τ → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ c', AnalyticAt ℂ (h' c') x) ∧
      ∀ᶠ z in 𝓝 x, (L z c - L x c) ^ r =
        ∑ i, h i z * f i z + ∑ c', h' c' z * (zeroCoordinate c (L z) c' - zeroCoordinate c (L x) c')) →
    ∃ (d : ℕ) (F : (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
      AnalyticAt ℂ F (L x) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
      (∀ᶠ z in 𝓝 x, F (L z) = ∑ i, h i z * f i z) ∧
      analyticOrderAt (fun s : ℂ => F (L x + Pi.single c s)) 0 = d

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjHomInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def FiniteProjHomInjective.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → (projHom J A).toRingHom.Finite →
      Function.Injective (projHom J A)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetsDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionSheetsDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N ∈ 𝓝 w, X ∩ N ⊆ closure {y | y ∈ X ∧ ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
      (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibreQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibreQuotient.Statement : Prop :=
  ∀ (B A : Type) [CommRing B] [CommRing A] (f : B →+* A), Function.Surjective f → IsNoetherianRing B →
    ∀ (m : Ideal A) (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      ∃ P' : PrimeSpectrum (AdicCompletion (m.comap f) B),
        P'.asIdeal.comap (algebraMap B (AdicCompletion (m.comap f) B)) =
            (P.comap (algebraMap A (AdicCompletion m A))).comap f ∧
          Nonempty (primeFibreLocalRing A P ≃+* primeFibreLocalRing B P'.asIdeal)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegularPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibresRegularPolynomial.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal →
    ∀ (P : Ideal (AdicCompletion M (MvPolynomial (Fin n) k))) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing (MvPolynomial (Fin n) k) P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFrameJacobianSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def frameProjLin {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ I :=
  (WithLp.linearEquiv 2 ℂ (I → ℂ)).symm.toLinearMap ∘ₗ LinearMap.pi fun i : I => innerₛₗ ℂ (b i)

theorem frameProjLin_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    WithLp.ofLp (frameProjLin b I z) = frameProj b I z := rfl

def FrameJacobianSum.Statement : Prop :=
  ∀ (d n : ℕ) (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))),
    areaJacobian (T.restrictScalars ℝ) =
      ∑ I ∈ Finset.univ.powersetCard d, areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphAreaHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def GraphAreaHolomorphic.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω → ∀ A ⊆ Ω, MeasurableSet A →
      μH[((2 * d : ℕ) : ℝ)] (graphPt e F '' A) =
        ∫⁻ x in A, ENNReal.ofReal (areaJacobian
          (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)))
          ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsIntegrallyClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsIntegrallyClosed.Statement : Prop :=
  ∀ (d : ℕ) (y : Fin d → ℂ), IsDomain (holGerms y) ∧ IsIntegrallyClosed (holGerms y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

