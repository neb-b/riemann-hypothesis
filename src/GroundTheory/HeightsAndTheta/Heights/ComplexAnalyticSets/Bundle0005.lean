module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericFibreRadical.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsRadical → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      (K.map (MvPolynomial.map (eval t))).IsRadical

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IsRadicalAway {R : Type*} [CommRing R] (K : Ideal R) (g : R) : Prop :=
  ∀ f ∈ K.radical, ∃ k : ℕ, g ^ k * f ∈ K

def fibreIdeal {σ : Type*} {n : ℕ} (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ))) (t : σ → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  K.map (MvPolynomial.map (eval t))

theorem fibreIdeal_map_C {σ : Type*} {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (t : σ → ℂ) :
    fibreIdeal (J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ))) t = J := by
  have h : (MvPolynomial.map (eval t)).comp (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ)) =
      RingHom.id (MvPolynomial (Fin n) ℂ) := by
    ext p <;> simp
  rw [fibreIdeal, Ideal.map_map, h, Ideal.map_id]

def GenericFibreRadicalAway.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (n : ℕ) (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ)))
    (g : MvPolynomial (Fin n) (MvPolynomial σ ℂ)), IsRadicalAway K g →
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      IsRadicalAway (fibreIdeal K t) (MvPolynomial.map (eval t) g)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericFibreRadicalPrime.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsPrime → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      (K.map (MvPolynomial.map (eval t))).IsRadical

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreTor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ker_fibreMap {σ ι : Type*} (t : σ → ℂ) :
    RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) =
      (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) :=
  MvPolynomial.ker_map _

def GenericFibreTor.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      L ⊓ RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) ≤
        RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) * L

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFreeness
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

def GenericFreeness.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] [Module.Finite B M],
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u

def GenericNoetherNormalisation.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (q : Ideal (MvPolynomial (Fin (n + 1)) A)),
    q.IsPrime → q ≠ ⊥ → q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥ →
    ∃ a : A, a ≠ 0 ∧ ∃ (z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q)
      (s : Finset (MvPolynomial (Fin (n + 1)) A ⧸ q)),
      ∀ d : MvPolynomial (Fin (n + 1)) A ⧸ q, ∃ (k : ℕ) (c : MvPolynomial (Fin (n + 1)) A ⧸ q → MvPolynomial (Fin n) A),
        a ^ k • d = ∑ t ∈ s, aeval z (c t) * t

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def GenericPrimitive.Statement : Prop :=
  ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (n : ℕ) (x : Fin n → L),
    IntermediateField.adjoin K (Set.range x) = ⊤ →
      ∃ D : MvPolynomial (Fin n) k, D ≠ 0 ∧ ∀ c : Fin n → k, MvPolynomial.eval c D ≠ 0 →
        IntermediateField.adjoin K {∑ j, c j • x j} = ⊤

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def graphJac {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  √(LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
    LinearMap.adjoint B ∘ₗ B))

def GraphJacContinuous.Statement : Prop :=
  ∀ (k m : ℕ) (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (ε : ℝ), 0 < ε →
    ∃ r : ℝ, 0 < r ∧ ∀ B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m), ‖B - A‖ ≤ r →
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∧
        graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGridProductLowerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def GridProductLowerBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (N : ℕ) (Z : Set (σ → ℂ)) (z₀ : σ → ℂ),
    Bornology.IsBounded Z → z₀ ∉ closure Z →
    ∃ μ : ℝ, 0 < μ ∧ ∃ U ∈ 𝓝 z₀, ∀ z ∈ U, ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) ⊆ Z → s.card ≤ N →
      ∃ u : σ → Fin (N + 1), μ ≤ ‖∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i)‖

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHausdorffNullComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory

def HausdorffNullComplementConnected.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (D C : Set E),
    IsOpen D → IsPreconnected D → μH[(Module.finrank ℝ E : ℝ) - 1] C = 0 → IsPreconnected (D \ C)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreInfinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def HolomorphicFibreInfinite.Statement : Prop :=
  ∀ (k d : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin d → ℂ),
    d < k → IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
      ∃ y : Fin d → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicIsolatedFibreOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def HolomorphicIsolatedFibreOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ) (u : Fin k → ℂ),
    IsOpen U → u ∈ U → DifferentiableOn ℂ g U →
    (∃ W ∈ 𝓝 u, ∀ v ∈ W, v ∈ U → g v = g u → v = u) →
    ∀ V ∈ 𝓝 u, g '' V ∈ 𝓝 (g u)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

