module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartSheetCompare
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm oneLine isSmoothHerm_oneLine)
open ComplexSets Matrix

def SegreChartSheetCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ J ∈ segreChartComponents P σ i, ∀ (A : Matrix (Fin e) (Fin m) ℂ) (x : Fin m → ℂ)
        (s : (Fin e → ℂ) → Fin m → ℂ), x ∈ zeroSet J → IsSheetAt J A x s →
          |ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ s) (A *ᵥ x)| ≤
            C * |ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x)|

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal PBlk)
open ComplexSets

def SegreChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal P → zeroSet (segreChartIdeal P σ i) = segreChartSet P σ i

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreSheetFormCompare
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm pot segre oneLine isSmoothHerm_oneLine)

def SegreSheetFormCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ (z : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ)) (y : Fin e → ℂ),
        IsOpen U → y ∈ U → DifferentiableOn ℂ z U → (∀ k, ∃ j, z y ⟨k, j⟩ ≠ 0) →
          |ReciprocityTheory.AnForm.maDens (fun j => pot L j ∘ z) y| ≤
            C * ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftBlockDatum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def liftCoords {ι' : Type} [Fintype ι'] {Ω : Type} (x' : ι' → Ω) : Fin (Fintype.card ι') → Ω :=
  fun j => x' ((Fintype.equivFin ι').symm j)

def LiftBlockDatum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a : ℕ)
    (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    1 ≤ a → (∀ j, x' j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) x' →
    Birational (fun p : Σ _ : Unit, ι' => x' p.2) →
    ∃ d : HSMBlockDatum D (Option K) (addIdx ι (Fintype.card ι')) Ω,
      d.y = addBlock y (liftCoords x') ∧ d.k₀ = none ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), ∀ j : Fin (Fintype.card ι'),
        secNormAt y N a (liftCoords x' j) (basePart₂ z) * d.A.h z = ‖z ⟨none, j⟩‖) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal d.y), basePart₂ z = w

end

end GroundTheory.Heights₂.Heights.Targets
end

