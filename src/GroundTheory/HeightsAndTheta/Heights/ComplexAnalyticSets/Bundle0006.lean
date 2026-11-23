module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicKernelFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolomorphicKernelFibre.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (b : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → b ∈ U →
    ∀ d : ℕ, Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) = d →
      ∃ (V : Set (Fin d → ℂ)) (y : Fin d → ℂ) (γ : (Fin d → ℂ) → Fin k → ℂ)
        (ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ),
        IsOpen V ∧ y ∈ V ∧ DifferentiableOn ℂ γ V ∧ Set.MapsTo γ V U ∧ Set.InjOn γ V ∧
          (∀ s ∈ V, ∀ t ∈ V, ℓ (f (γ s)) = ℓ (f (γ t)) → f (γ s) = f (γ t)) ∧
          fderiv ℂ (fun t => ℓ (f (γ t))) y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicOnSubset
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolomorphicOnSubset {σ : Type*} [Fintype σ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (σ → ℂ) → E) (S : Set (σ → ℂ)) : Prop :=
  ∀ z ∈ S, ∃ U : Set (σ → ℂ), IsOpen U ∧ z ∈ U ∧ ∃ F : (σ → ℂ) → E,
    DifferentiableOn ℂ F U ∧ Set.EqOn f F (S ∩ U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicZeroSetDimH
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric
open scoped ENNReal

def HolomorphicZeroSetDimH.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (h : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ h U →
    (∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0) →
      dimH {v | v ∈ U ∧ h v = 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHypersurfacePresentation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def HypersurfacePresentation.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsPrime → (∀ s : MvPolynomial σ ℂ, C s ∈ K → s = 0) →
    ∃ (d : ℕ) (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
      (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
      (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
      (u v : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      m.Monic ∧ D ≠ 0 ∧ u * m + v * Polynomial.derivative m = Polynomial.C D ∧
      (∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
        Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H) ∧
      ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIdealHeightSpread
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def IdealHeightSpread.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I P : Ideal R) [P.IsPrime], I ≤ P →
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], I ≤ Q → g ∉ Q →
      (I.map (algebraMap R (Localization.AtPrime P))).height ≤
        (I.map (algebraMap R (Localization.AtPrime Q))).height

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImplicitCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology

noncomputable section

def ImplicitCurve.Statement : Prop :=
  ∀ (n k : ℕ) (γ : (Fin (k + 1) → ℂ) → Fin n → ℂ) (R : ℝ) (L : Matrix (Fin k) (Fin n) ℂ)
    (s : Fin (k + 1) → ℂ),
    DifferentiableOn ℂ γ (Metric.ball 0 R) → s ∈ Metric.ball 0 R →
    Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ t)) s) →
      ∃ r > 0, ∃ φ : (Fin 1 → ℂ) → Fin (k + 1) → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ φ 0 = s ∧
        (∀ τ ∈ Metric.ball 0 r,
          φ τ ∈ Metric.ball 0 R ∧ φ τ 0 = s 0 + τ 0 ∧ L *ᵥ γ (φ τ) = L *ᵥ γ s) ∧
        ∃ P ∈ 𝓝 s, ∀ t ∈ P, L *ᵥ γ t = L *ᵥ γ s → ∃ τ ∈ Metric.ball 0 r, φ τ = t

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicDerivNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def InjectiveHolomorphicDerivNeZero.Statement : Prop :=
  ∀ (D : Set ℂ) (f : ℂ → ℂ), IsOpen D → DifferentiableOn ℂ f D → Set.InjOn f D → ∀ a ∈ D, deriv f a ≠ 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U → IsOpen (f '' U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInvarianceOfDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InvarianceOfDomain.Statement : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → Fin n → ℝ),
    IsOpen U → ContinuousOn f U → Set.InjOn f U → IsOpen (f '' U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreLocalUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsolatedFibreLocalUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B, (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ B ∩ W, A x = A w → x = w) →
    ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), M ∈ 𝓝 w ∧ AnalyticAt ℂ g (A w) ∧
      (¬ ∀ᶠ y in 𝓝 (A w), g y = 0) ∧
      ∀ x ∈ X ∩ B ∩ M, g (A x) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutGlobal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutGlobal.Statement : Prop :=
  ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
    IsNilpotent P → IsPrincipalIdealRing (C ⧸ P) → y ∉ P → (P ⊔ Ideal.span {y}).IsMaximal →
      (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (M ⧸ (Ideal.span {y} • ⊤ : Submodule C M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutLocalizedModule
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutLocalizedModule.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B) (Q₀ : Ideal B) [Q₀.IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M],
    IsNilpotent P → y ∉ P → Q₀ = P ⊔ Ideal.span {y} → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length (Localization.AtPrime Q₀)
          (LocalizedModule Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M))) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
end

