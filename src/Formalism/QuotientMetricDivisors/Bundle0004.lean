module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.QuotientMetricDivisors.Bundle0003
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.LogFactorialIndices.Bundle0001
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.PassageScaleFree
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K]

def scaleFrame {d : ℕ} (t : InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) :
    InfinitePlace K → Matrix (Fin d) (Fin d) ℂ :=
  fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v

end Defs

def KappaInvariance : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ t : InfinitePlace K → ℝ, (∀ v, 0 < t v) →

      (∀ v, IsUnit (scaleFrame t XE v).det ∧
        ((scaleFrame t XE v)⁻¹).conjTranspose * (scaleFrame t XE v)⁻¹ =
          (t v : ℂ) • (((XE v)⁻¹).conjTranspose * (XE v)⁻¹)) ∧

      (∀ (d : ℕ) (XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (φ : Matrix (Fin D) (Fin d) K)
        (v : InfinitePlace K),
        detRatio XS (scaleFrame t XE) φ v = t v ^ d * detRatio XS XE φ v) ∧
      (∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
        meanLog (fun v => t v * κ v) = meanLog t + meanLog κ) ∧

      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
        lcv (scaleFrame t XE) R = lcv XE R + (D : ℝ) * meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE))
                  (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
            meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)) XE R - meanLog t ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R - meanLog t) ∧

      (∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
        ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                  (Formalism.HN.dualFrame (scaleFrame t XE)) φ =
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame XE) φ - meanLog t)

def KappaNormalise : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
      (∀ v, IsUnit (scaleFrame (fun v => (κ v)⁻¹) XE v).det) ∧

      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (ρ P : ℝ), detRatio XS XE φ v = (κ v * ρ) ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 * ρ) ^ D * P) ∧
      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (P : ℝ), detRatio XS XE φ v = κ v ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 : ℝ) ^ D * P) ∧
      meanLog (fun _ : InfinitePlace K => (1 : ℝ)) = 0 ∧
      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) + meanLog κ ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R - meanLog κ ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                  Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
            Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R ∧
        ∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
          ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
              (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ - meanLog κ ∧
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                    Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
              Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.TheoremDivIneqRows
section
open Finset

noncomputable section

namespace Formalism.DivisionValues

def phRows (lam : Multiset ℕ) : ℝ := (lam.map fun r : ℕ => Formalism.LatticeIndexTer.ph (r : ℝ)).sum

def logFactRows (lam : Multiset ℕ) : ℝ := (lam.map fun r : ℕ => Real.log (r.factorial : ℝ)).sum

def IsRowsOff (n w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin (n + 1) → ℕ) (c' r : Fin n → ℕ) (blk sm : Multiset ℕ),
    Formalism.LatticeIndexTer.Interlaced n (fun i => (c i : ℝ)) (fun i => (c' i : ℝ)) S ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (Finset.univ.val.map fun i => w + c i) + blk ∧
    ap = Finset.univ.val.map r + sm

def IsRowsTop (n aT w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin n → ℕ) (c' r : Fin (n + 1) → ℕ) (r0 : ℕ) (blk sm : Multiset ℕ),
    Formalism.LatticeIndexTer.Interlaced n (fun i => (c' i : ℝ)) (fun i => (c i : ℝ)) S ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    r0 ≤ w ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk) ∧
    ap = Finset.univ.val.map r + sm

def RowsFactorial : Prop :=
  ∀ (n w : ℕ) (S Bl sh A La fa : ℝ) (ν ap : Multiset ℕ),
    La = Real.log A → 1 ≤ La → (w : ℝ) + S ≤ A → Bl ≤ A → logFactRows ap ≤ fa →
    (IsRowsOff n w S Bl sh ν ap →
      phRows ν - fa ≤ ((w : ℝ) + 2 * S + (n : ℝ) * sh + Bl) * La) ∧
    (∀ aT : ℕ, (aT : ℝ) + (w : ℝ) ≤ A → IsRowsTop n aT w S Bl sh ν ap →
      phRows ν - fa ≤
        Formalism.LatticeIndexTer.ph (aT : ℝ) + ((2 * (w : ℝ) + S + (n : ℝ) * sh + Bl) * La + 1))

def RowsPeriod : Prop :=
  ∀ (n w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ),
    (IsRowsOff n w S Bl sh ν ap →
      0 ≤ (ν.sum : ℝ) - ((n : ℝ) + 1) * (w : ℝ) ∧
      (ν.sum : ℝ) - ((n : ℝ) + 1) * (w : ℝ) ≤ ((n : ℝ) + 1) * S + Bl) ∧
    (∀ aT : ℕ, IsRowsTop n aT w S Bl sh ν ap →
      -(w : ℝ) ≤ (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ∧
      (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ≤ (n : ℝ) * S + Bl)

def RowsHook : Prop :=
  ∀ μ : YoungDiagram,
    logFactRows (μ.rowLens : Multiset ℕ) ≤ Real.log (Formalism.LatticeIndexTer.hookProd μ : ℝ)

def RowsStepE : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n : ℕ) (aT : Pl → ℕ) (w : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc t η m b' cs C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs →

    2 ≤ C0 → cs + 1 ≤ C0 → 2 * Sc ≤ C0 * S →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * (t + 1) * η ≤ a * rd →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0)))

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.UntwistedChoice
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def PrimeSumSq : Prop :=
  (∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
    ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 999 / 1000) ∧
  Summable (fun p : Nat.Primes => 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) ∧
  ∑' p : Nat.Primes, 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 < 1

def PlaceSumNat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (n : K) : ℝ)).Finite ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (n : K) : ℝ) = Real.log (n : ℝ) ∧
    ∀ S : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ)

def UntwistedChoice : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S Tw : Finset Pl) (D : ℕ), 0 < D → Tw ⊆ S →
    ∀ (l ell : Pl → ℝ) (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w ∈ S, w ∉ Tw → ∀ j, I w j + Ic w j + jT w j = 0) →
    (∀ w ∈ S, w ∉ Tw → ∀ j, F w j = 0) →
    (∀ w ∈ Tw, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ Tw, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    ∃ err' Jx' η' : Pl → J → ℝ,
      (∀ w ∈ Tw, ∀ j, err' w j = err w j ∧ Jx' w j = Jx w j ∧ η' w j = η w j) ∧
      (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err' w j) + 2 / ell w ^ 2) * D) ∧
      (∀ w ∈ S, ∀ j, jT w j ≤ Jx' w j * D + η' w j) ∧
      (∀ j, ∑ w ∈ S, l w * (err' w j + Jx' w j) = ∑ w ∈ Tw, l w * (err w j + Jx w j)) ∧
      (∀ j, ∑ w ∈ S, l w * η' w j / D = ∑ w ∈ Tw, l w * η w j / D) ∧
      (∀ j, ∑ w ∈ S, l w * F w j = ∑ w ∈ Tw, l w * F w j)

end Formalism.DivisionValues
end
end

