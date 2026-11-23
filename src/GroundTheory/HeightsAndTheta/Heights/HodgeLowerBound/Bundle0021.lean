module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ModelPtsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (n : ℕ) (ψ : Fin n → OpenPartialHomeomorph M.Xc (Fin e → ℂ)) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (E : Set M.Xc) (v : M.Xc → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm L → IsPtsNull P e N →
    (∀ j, IsCompatChart M.atlas (ψ j)) → (∀ x, ∃ j, x ∈ (ψ j).source) →
    (∀ j, volume ((ψ j).target ∩ (ψ j).symm ⁻¹' E) = 0) →
    (∀ j, ∀ Q ⊆ (ψ j).target, IsCompact Q → IntegrableOn (fun y => v ((ψ j).symm y)) Q) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∉ E → g z = v (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRefAlongSheet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RefAlongSheet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (S : LogLogRegularisationSetting M Xo A)
    (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) (j : Fin S.R.N),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P) →
    M.proj (γ y) ∈ (S.R.chart j).source →
    (∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (S.R.chart j).source ∧
      DifferentiableAt ℂ (fun y'' => S.R.chart j (M.proj (γ y''))) y') →
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G y ∧ ∀ᶠ y' in 𝓝 y,
      Real.log (S.ref.h (γ y')) = S.R.q j (S.R.chart j (M.proj (γ y'))) + (G y').re

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsSheetChartHolo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

def SheetChartHolo.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (R : RegChartData M.atlas) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    ∀ᵐ y : Fin n → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ),
      IsSheet P Q y w γ → ∃ j : Fin R.N, M.proj (γ y) ∈ (R.chart j).source ∧ M.proj (γ y) ∈ R.Yo ∧
        ∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (R.chart j).source ∧
          DifferentiableAt ℂ (fun y'' => R.chart j (M.proj (γ y''))) y'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

