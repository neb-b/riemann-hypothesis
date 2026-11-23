module

public import Mathlib
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.MirabolicMackeyTheory.Bundle0001

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisorInequality

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)

def BoundsMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), 0 < D → (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ y, μ (conjPl y) = μ y) →
    {y | μ y ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsFullLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J]
      (XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : J → Submodule (𝓞 K) (Fin D → K)), (∀ j, Submodule.IsFullLattice K (M j)) →
    ∀ (HT : J → Tup → Matrix (Fin D) (Fin D) K)
      (XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (Tl : J → Tup → Submodule (𝓞 K) (Fin D → K)), (∀ j t, Submodule.IsFullLattice K (Tl j t)) →
    ∀ (θ : J → Tup → Matrix (Fin D) (Fin D) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρt : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρt t) = (ρr t : ℂ)) → ρt μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ y, vw y (ρt (μ y)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (Gm : Tup → HeightOneSpectrum (𝓞 K) → K)
      (eb : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t y, IsLocBasis (abelian₂ t) y (eb t y)) →
    (∀ t y, v0.embedding (Gm t y) = (gram (XQ t) v0 (eb t y)).det) →
    ∀ (nH : ℕ) (Hm : Matrix (Fin nH) (Fin nH) K), (∀ i j, Hm i j ∈ K0) →
    (∀ v : InfinitePlace K, (Hm.map v.embedding).PosDef) →
    ∀ Pm : Matrix (Fin D) (Fin nH) K, Function.Surjective Pm.mulVec → IsQuotMetric Pm Hm (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin nH → K), Submodule.IsFullLattice K Mt → abelian₂ μ0 = matLat Pm Mt →
    (∀ y, Gm μ0 y = gramR (quotGram Pm Hm) (eb μ0 y)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
    (∀ y, Formalism.HermitianLatticesTheory.localization₂ y.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))) →

    ∀ (Sy Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ Sy →
    (∀ y ∉ Sy, lw y * ((vw y (Gm (μ y) y) : ℝ) + ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ))) = 0) →
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) = 0) →
    ∀ (LG E3 : ℝ) (E1 E2 : J → ℝ) (elly gy : HeightOneSpectrum (𝓞 K) → ℝ)
      (Fy erry Jy ηy : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, Fy y j = 0) →

    (∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y) → ∑ y ∈ Sy, lw y * gy y ≤ LG →

    (∀ y ∈ Tw, ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
        (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ)) ≤
      (∑ j, (2 * Fy y j + erry y j) + 2 / elly y ^ 2) * D) →

    (∀ y ∈ Tw, ∀ j, (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) ≤ Jy y j * D + ηy y j) →

    (∀ j, ∑ y ∈ Tw, lw y * (erry y j + Jy y j) ≤ E1 j) →
    (∀ j, ∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j) →
    ∑ y ∈ Sy, lw y * (2 / elly y ^ 2) ≤ E3 →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) ≤
        meanLog κ + (∑ j, lcv (XW j) (M j) / D) + 2 * (∑ j, ∑ y ∈ Tw, lw y * Fy y j) + LG +
          (∑ j, (E1 j + E2 j)) + E3 ∧
      ∀ j, lcv (XW j) (M j) / D = -Formalism.HN.muDef (Pi.basisFun K (Fin D)) (XW j) (M j)

end Formalism.DivisorInequality
