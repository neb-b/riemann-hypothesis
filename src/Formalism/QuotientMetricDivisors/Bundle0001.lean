module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HarderNarasimhan.Bundle0001
public import Formalism.LogFactorialIndices.Bundle0001

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.ClassSumDualLe
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cutLat {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  A.comap ((Matrix.mulVecLin E).restrictScalars (𝓞 K))

def IsOrthProj {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) : Prop :=
  Pr * E = 1 ∧ Eᴴ * H * (1 - E * Pr) = 0

def IsClassSum {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    (H : Matrix (Fin n) (Fin n) K) (I : (Fin n → K) →ₗ[K] (Cl → V))
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (g : Cl → ℕ) : Prop :=
  ∀ x y, hform H x y = ∑ c, ((g c : K))⁻¹ * pair (I x c) (I y c)

end Defs

def OrthProjExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      Hᴴ = H ∧ IsUnit H.det ∧ IsUnit (Eᴴ * H * E).det ∧
        IsOrthProj H E ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)) ∧
        ∀ Pr, IsOrthProj H E Pr → Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H)

def ProjDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A) = cutLat E (Formalism.HermitianLatticesTheory.dual (hform H) A)

def CutDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K A →
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (cutLat E A) = matLat Pr (Formalism.HermitianLatticesTheory.dual (hform H) A)

def ExpIndexLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (A B : Submodule (𝓞 K) (Fin D → K)), Submodule.IsFullLattice K A → Submodule.IsFullLattice K B →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ x ∈ A, a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) →
      idx w A B ≤ (D : ℤ) * vw w (a : K)

def ProjIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G0 : Type) [Fintype G0]
    (r : G0 → Matrix (Fin n) (Fin n) K) (c : G0 → K) (G : ℕ),
    (∀ s, ∃ a : 𝓞 K, (a : K) = (G : K) * c s) →
    ∀ B : Submodule (𝓞 K) (Fin n → K), (∀ s, ∀ x ∈ B, (r s).mulVec x ∈ B) →
    ∀ x ∈ B, (G : 𝓞 K) • (∑ s, c s • r s).mulVec x ∈ B

def BoundsI : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsFullLattice K A →
    ∀ s : ℕ, (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ G : ℕ, (∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A) →
      Submodule.IsFullLattice K (cutLat E A) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E A), ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E A

def BoundsIVGen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ z ∈ cutLat E A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsFullLattice K (matLat Pr A) ∧ Submodule.IsFullLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * (vw w (a : K) + vw w (DG : K))

def BoundsIV : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E A, (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsFullLattice K (matLat Pr A) ∧ Submodule.IsFullLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K))

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.DualMu
section
open Module NumberField

noncomputable section

namespace Formalism.DivisionValues

def DualMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame X) (Formalism.HN.dualLat R) =
        lcv X R / D

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.LatticeGlueUnique
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

def glueLat {K : Type} [Field K] [NumberField K] {D : ℕ}
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin D → K) :=
  ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

def LatticeGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsFullLattice K L0 → (∀ w, Submodule.IsFullLattice K (L w)) →
    {w : HeightOneSpectrum (𝓞 K) |
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0}.Finite →
    Submodule.IsFullLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.ProdFormula
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a : K), a ≠ 0 →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)).Finite ∧
    (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ =
      ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w a : ℝ)

def DetCS : Prop :=
  ∀ (n D : ℕ) (Hc : Matrix (Fin n) (Fin n) ℂ), Hc.PosDef →
    ∀ A B : Matrix (Fin D) (Fin n) ℂ,
      ‖(A * Hc * Bᴴ).det‖ ^ 2 ≤ (A * Hc * Aᴴ).det.re * (B * Hc * Bᴴ).det.re

def LcvBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)).Finite ∧
      lcv X L = (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (gram X v e).det.re +
        2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)

def IdxChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (L : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (γ : Matrix (Fin d) (Fin d) K),
      IsLocBasis L w (fun i => ∑ k, γ k i • e k) →
      idx w (Submodule.span (𝓞 K) (Set.range e)) L = vw w γ.det ∧
      idx (conjPl w) (Submodule.span (𝓞 K) (Set.range e)) L = vw (conjPl w) γ.det

def ValBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b) ∧
    (∀ a : K, vw w (star a) = vw (conjPl w) a) ∧
    lw (conjPl w) = lw w ∧ conjPl (conjPl w) = w ∧ vw w 1 = 0 ∧
    (∀ a : K, vw w a⁻¹ = - vw w a) ∧
    (∀ a : 𝓞 K, 0 ≤ vw w (a : K))

def GramChange : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (D m : ℕ) (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) (γ : Matrix (Fin m) (Fin m) K),
      gramR Γ (fun i => ∑ k, γ k i • e k) = star γ.det * γ.det * gramR Γ e

def ImageLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (XS v).det) →
    (∀ v, IsUnit (XT v).det) →
    ∀ φ : Matrix (Fin d) (Fin d) K, IsUnit φ.det →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L →
      lcv XT (matLat φ L) = lcv XS L + (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (detRatio XS XT φ v)

def IdxLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A B : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K A → Submodule.IsFullLattice K B →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite ∧
      lcv X B = lcv X A + 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w A B : ℝ)

def RatHermLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K T →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (jw H w T : ℝ)).Finite ∧
      lcv X T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw H w T : ℝ)

def JwGram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K), IsLocBasis T w f →
      jw H w T = - vw w (gramR H f)

def FinsumConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (f : HeightOneSpectrum (𝓞 K) → ℝ),
    ∑ᶠ w, f (conjPl w) = ∑ᶠ w, f w

def LocBasisEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (L : Submodule (𝓞 K) (Fin d → K)),
    Submodule.IsFullLattice K L → ∀ w : HeightOneSpectrum (𝓞 K), ∃ f : Fin d → Fin d → K, IsLocBasis L w f

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows
section
open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

def PrimeLogSum : Prop :=
  ∀ (Y : ℝ), 1 ≤ Y → ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y + Real.log 4

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.StatementACE
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

def StepA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (n D : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (π : Matrix (Fin D) (Fin n) K)
    (ι : Matrix (Fin D) (Fin D) K)
    (B : (Fin D → K) →ₗ[K] K) (P : (Fin n → K) →ₗ[K] K) (ζ : K) (σ : ℤ),
    ζ ≠ 0 → vw w ζ = 0 →
    (∀ F : Fin n → K, P F = ζ * B (ι.mulVec (π.mulVec F))) →
    (∀ F ∈ M, P F = 0 ∨ σ ≤ vw w (P F)) →
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat π M)), B x = 0 ∨ σ ≤ vw w (B x)

def BoundsSum : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S : Finset Pl) (D : ℕ), 0 < D →
    ∀ (lcvR logκ LG E3 : ℝ) (lcvM L E1 E2 : J → ℝ) (l ell vG g : Pl → ℝ)
      (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w, 0 ≤ l w) →
    lcvR ≤ (D : ℝ) * logκ + ∑ j, lcvM j +
      ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) →
    (∀ w ∈ S, vG w ≤ (D : ℝ) * g w) → ∑ w ∈ S, l w * g w ≤ LG →
    (∀ j, lcvM j / D ≤ L j) →
    (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, l w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, l w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ E3 →
      lcvR / D ≤ logκ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, l w * F w j + LG + ∑ j, (E1 j + E2 j) + E3

end Formalism.DivisionValues
end
end

