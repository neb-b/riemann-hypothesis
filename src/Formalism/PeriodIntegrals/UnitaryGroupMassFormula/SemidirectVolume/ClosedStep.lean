module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def ratG {X : Type} [Group X] (Γ K : Subgroup X) : Subgroup K := (Γ ⊓ K).subgroupOf K

def LCSC (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  LocallyCompactSpace G ∧ SecondCountableTopology G ∧ T2Space G ∧ IsTopologicalGroup G

def DiscC {X : Type} [Group X] [TopologicalSpace X] (Γ K : Subgroup X) : Prop :=
  Countable (ratG Γ K) ∧ DiscreteTopology (ratG Γ K)

def Semi {X : Type} [Group X] [TopologicalSpace X] (K N H : Subgroup X) : Prop :=
  (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
    ∃ e : (N × H) ≃ₜ K, ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X)

def ConjInv {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X] (N H : Subgroup X) : Prop :=
  ∀ μN : Measure N, μN.IsHaarMeasure → ∀ h ∈ H, ∀ f : X → ENNReal, Measurable f →
    ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μN = ∫⁻ n, f (n : X) ∂μN

def ProdF {X : Type} [Group X] [MeasurableSpace X] (K N H : Subgroup X)
    (μK : Measure K) (μN : Measure N) (μH : Measure H) : Prop :=
  ∀ f : X → ENNReal, Measurable f →
    ∫⁻ k, f (k : X) ∂μK = ∫⁻ m, ∫⁻ h, f ((m : X) * (h : X)) ∂μH ∂μN

def SubLCSC : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] (Γ K : Subgroup X), LCSC X → IsClosed (K : Set X) →
    Countable Γ → DiscreteTopology Γ → LCSC K ∧ DiscC Γ K

def ProdHaarG : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (K N H : Subgroup X), Semi K N H → LCSC K → LCSC N → LCSC H → ConjInv N H →
    ∀ μN : Measure N, μN.IsHaarMeasure → ∀ μH : Measure H, μH.IsHaarMeasure →
    ∃ μK : Measure K, μK.IsHaarMeasure ∧ ProdF K N H μK μN μH

def DiscHA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    Countable (HFinIn (AF F) σ J) ∧ DiscreteTopology (HFinIn (AF F) σ J)

def TensTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) ∧
      LocallyCompactSpace (AF F ⊗[F] E) ∧ SecondCountableTopology (AF F ⊗[F] E)

end PI.VolSemiDirect.W
