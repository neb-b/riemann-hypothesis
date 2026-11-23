module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMoriwakiBigCurve

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSheetSimpleNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def IsSimpleSheetPt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSheet P Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ q.1 → q.2 = segre (γ q.1)

def PtsSheetSimpleNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      volume {y : Fin e → ℂ | ∃ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) ∧ ¬ IsSimpleSheetPt P Ψ w} = 0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSumMeasurable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsSumMeasurable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (L j)) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A →
    IsSectionOn P A s →
    AEStronglyMeasurable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w) volume

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

def SegreChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsArithVar P (e + 1) → ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def SegreChartIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin (e + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin (e + 1) → (Fin m → ℂ) → ℝ),
    IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g → 0 < δ →
    ((∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) ∨
      ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → pot L 0 z = 0) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ptsIntegral P (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegralPoints
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar ptsIntegral pot segre PBlk)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents chartLift)

def SegreChartIntegralPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin 0 → (Fin m → ℂ) → ℝ),
    IsArithVar P 1 → IsDegZeroSmooth g → 0 < δ →
    (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    (∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ chartLift σ i) →
      ptsIntegral P (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J 0 G Φ

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveCountLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo

def CurveCountLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y → IsSmoothHerm A →
    IsConjInvariantH A →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      (τ : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ

namespace CurveCountLower

end CurveCountLower

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Stokes
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre)

theorem StokesStatement.of_found (hBil : PtsBilinear.Statement) (hPart : SegrePartition.Statement)
    (hChart : SegreChart.Statement) (hSV : StokesOnVariety.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by
  classical
  intro K _ ι _ P n L B B' hP hL hB hB' hB0 hB'0
  have hw := isDegZeroSmooth_log hB hB0
  have hw' := isDegZeroSmooth_log hB' hB'0
  have hne : ∀ k, Nonempty (ι k) := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    exact ⟨i⟩
  obtain ⟨δ, hδ, ρ, hρs, hρ1, hρ0⟩ := hPart K ι hne

  have hpiece : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρs i).mul hw

  have key : ∀ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
        (fun z => ρ i z * Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
        (fun z => Real.log (B'.h z)) := by
    intro i
    obtain ⟨m, Js, U, V, Φ, hJ, hU, h1, h2⟩ := hChart K ι P n L (fun z => ρ i z * Real.log (B.h z))
      (fun z => Real.log (B'.h z)) i δ hP hL (hpiece i) hw' hδ
      (fun z hz => by simp only [hρ0 i z hz, zero_mul])
    rw [h1, h2]
    refine Finset.sum_congr rfl fun J hJs => ?_
    obtain ⟨hJp, hJd, hUs, hVs, hΦs⟩ := hJ J hJs
    exact hSV m n J U V Φ hJp hJd hUs hVs hΦs (Or.inl hU)
  have hsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) := by
    funext z
    rw [← Finset.sum_mul, hρ1 z, one_mul]
  obtain ⟨hA, hC⟩ := hBil K ι P n L _ (fun i z => ρ i z * Real.log (B.h z))
    (fun z => Real.log (B'.h z)) hP hL hpiece hw'
  calc ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (fun z => Real.log (B.h z))
      = ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ∑ i, ρ i z * Real.log (B.h z)) := by rw [← hsum]
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ρ i z * Real.log (B.h z)) := hA
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := Finset.sum_congr rfl fun i _ => key i
    _ = ptsIntegral P (Fin.cons (fun z => ∑ i, ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := hC.symm
    _ = ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := by rw [← hsum]

end GroundTheory.Heights₂.Heights
end

