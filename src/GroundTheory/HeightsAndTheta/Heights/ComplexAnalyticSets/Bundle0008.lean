module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjDimSpread
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open CategoryTheory

def ProjDimSpread.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I P : Ideal R) [P.IsPrime] (ℓ : ℕ),
    HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))) ℓ →
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))) ℓ

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperHolomorphicSurjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def ProperHolomorphicSurjective.Statement : Prop :=
  ∀ (k : ℕ) (Ω D : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen Ω → Ω.Nonempty → IsOpen D → IsPreconnected D → DifferentiableOn ℂ g Ω → Set.MapsTo g Ω D →
    (∀ L ⊆ D, IsCompact L → IsCompact (Ω ∩ g ⁻¹' L)) →
    g '' Ω = D

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionBranchLocus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionBranchLocus.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → IsPreconnected D → D.Nonempty → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∃ δ : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
      ∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → IsPreconnected D → D.Nonempty → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
      AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = N) ∧
      (∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O) ∧
      X ∩ B ⊆ closure {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionLocalCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionLocalCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ) (n : ℕ),
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
      (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
      (∀ y ∈ U, {x | x ∈ X ∩ B ∧ A x = y}.encard ≤ n) ∧
      ∀ y ∈ U, g y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = n ∧
        ∀ x ∈ X ∩ B, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionLocalUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionLocalUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
      (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
      ∀ y ∈ U, g y ≠ 0 →
        ∀ x ∈ X ∩ B, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperSheetedFibreEsymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperSheetedFibreEsymm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    AnalyticOnNhd ℂ δ D →
    (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0) →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∃ F : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ F D ∧
      ∀ t ∈ D, δ t ≠ 0 → ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = t} →
        F t = (s.val.map l).esymm j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRankDeficientFibreInfinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def RankDeficientFibreInfinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
    (∀ v ∈ U, ¬ Function.Injective (fderiv ℂ f v)) →
      ∃ y : Fin m → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularSequenceLengthLeDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

universe u

def RegularSequenceLengthLeDim.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → (rs.length : WithBot ℕ∞) ≤ ringKrullDim R

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

noncomputable section

def RiemannExtensionAnalytic.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g f : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U →
    (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0) →
    DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}) →
    (∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0}))) →
    ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U ∩ {t | g t ≠ 0})

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRootSumHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def RootSumHolomorphic.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (W : Set (Fin d → ℂ)) (Φ : (Fin d → ℂ) → ℂ → ℂ),
    m.Monic → IsOpen W → (∀ y ∈ W, (m.map (MvPolynomial.eval y)).Separable) →
    (∀ y ∈ W, ∀ τ : ℂ, (m.map (MvPolynomial.eval y)).IsRoot τ →
      ∃ O : Set ((Fin d → ℂ) × ℂ), IsOpen O ∧ (y, τ) ∈ O ∧ ∃ Ψ : (Fin d → ℂ) × ℂ → ℂ,
        DifferentiableOn ℂ Ψ O ∧
        ∀ p ∈ O, (m.map (MvPolynomial.eval p.1)).IsRoot p.2 → Φ p.1 p.2 = Ψ p) →
    DifferentiableOn ℂ (fun y => ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum) W

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRueckertNullstellensatz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def RueckertNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (f i) w) → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, (∀ i, f i z = 0) → g z = 0) →
    ∃ (m : ℕ) (h : Fin k → (σ → ℂ) → ℂ), 0 < m ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
      ∀ᶠ z in 𝓝 w, g z ^ m = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

