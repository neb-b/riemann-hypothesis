module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegreeIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionDegreeIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    A₀.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → A₁.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A₀ → IsSmoothHerm A₁ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) =
        (genDeg (mCoordIdeal d.y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionImageSup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def BlockResolutionImageSup.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRingOver ℂ ι, IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ x : d.R.X,
        ‖eval (blockPt d x) f‖ / d.A.h (blockPt d x) ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionInterpIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionInterpIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A' →
    ((D : ℝ) + 1) * blockMetricInt d A' =
      ∑ i ∈ Finset.range (D + 1),
        mInt d.R.A
          (fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMetricPair
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def BlockResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι)),
    A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → P0' ≤ mCoordIdeal d.y → IsSemipositiveRel P0' (mCoordIdeal d.y) A' →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Σ k, ι k) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
        (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) →
          σ n b (chartIdx A y) y = eval (fun p => c p.1 * blockPt d y p) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.A.h (fun p => c p.1 * blockPt d y p)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (A'.h (fun p => c p.1 * blockPt d y p))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => blockInterpPot d d.A A' t) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    (∀ j, IsSmoothHerm (L j)) → A₁.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A₁ →
    ptsIntegral (mCoordIdeal d.y) (fun j z => Real.log ((L j).h z)) (fun z => Real.log (A₁.h z / d.A.h z)) =
      mInt d.R.A (fun j => AnResBridge.potOf d.R (L j))
        (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A' →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (mCoordIdeal d.y) (blockMixPot d.A A' D i) (fun z => Real.log (A'.h z / d.A.h z)) =
      ((D : ℝ) + 1) * blockMetricInt d A'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartConstantsDetermined
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def intsIn (F Ω : Type*) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] : Subalgebra ℤ Ω :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.range

def ChartConstantsDetermined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ w w' : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def ChartTaylorCover.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A),
    ∃ r : ℝ, 0 < r ∧ ∃ M c : ℝ, 0 < c ∧ ∀ x : X, ∃ j : Fin A.n, x ∈ (A.chart j).source ∧
      Metric.closedBall (A.chart j x) r ⊆ (A.chart j).target ∧
      (∀ y ∈ Metric.closedBall (A.chart j x) r, c ≤ dV.dens j y) ∧
      ∀ W ∈ [W₀, W₁], ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + M * ∑ i, ‖z i‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (b : K → ℤ) (τ : ℕ) (s : Ω),
    s ∈ chartLatQ y b τ → ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * s ∈ chartLat y b τ

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDiagonalSectionDifference
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def DiagonalSectionDifference.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) →
    ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) + C * (j : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def EmbeddingPieces.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : (F →+* ℂ) → ℝ)
    (w : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → w =ᶠ[𝓝 z] fun _ => c sg) →
    ptsIntegral (mCoordIdeal y) (pot L) w =
      (∑ sg, c sg) / Fintype.card (F →+* ℂ) * ptsIntegral (mCoordIdeal y) (pot L) (fun _ => 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSectionsPower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def EuclideanSectionsPower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        IsSmallH (mCoordIdeal y) y A k (t : Ω) → (st : Ω) = s * t → ‖φ (n + k) st‖ ≤ ‖φ n s‖) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop,
        ∀ [DiscreteTopology (imageLattice (φ (m * q)))] [IsZLattice ℝ (imageLattice (φ (m * q)))],
          -Real.log (ZLattice.covolume (imageLattice (φ (m * q)))) ≤
            (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
              (((m * q : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

