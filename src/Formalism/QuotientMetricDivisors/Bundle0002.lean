module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LogFactorialIndices.Bundle0001
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HarderNarasimhan.Bundle0001

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.ClassSumDualGeF
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def valLatF {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V) :
    Submodule (𝓞 K) (Fin n → K) :=
  (Submodule.pi Set.univ N).comap (I.restrictScalars (𝓞 K))

end Defs

def ClassSumDualLeF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K),
    pair.IsSymm → pair.Nondegenerate →
    ∀ (Gam : Cl → Type) [∀ c, Group (Gam c)] [∀ c, Fintype (Gam c)]
      (ρ : ∀ c, Gam c →* Module.End K V),
    (∀ c γ x y, pair (ρ c γ x) (ρ c γ y) = pair x y) →
    ∀ I : (Fin n → K) →ₗ[K] (Cl → V),
    (∀ f : Cl → V, (∃ x, I x = f) ↔ ∀ c γ, ρ c γ (f c) = f c) →
    IsClassSum H I pair (fun c => Fintype.card (Gam c)) →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsFullLattice K (Nab c)) →
    ∀ s : ℕ, (∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c), (s : 𝓞 K) • y ∈ Del c) →
    (∀ c γ, ∀ y ∈ Del c, ρ c γ y ∈ Del c) →
    ∀ y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLatF I Nab), (s : 𝓞 K) • y ∈ valLatF I Del

def ClassSumDualGeF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), (∀ c, 0 < g c) → IsClassSum H I pair g →
    ∀ (Nab Del : Cl → Submodule (𝓞 K) V) (s : ℕ),
    (∀ c, ∀ y ∈ Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c)) →
    ∀ DG : ℕ, (∀ c, g c ∣ DG) →
    ∀ y ∈ valLatF I Del, ((DG * s : ℕ) : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLatF I Nab)

def BoundsIClassF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K),
    pair.IsSymm → pair.Nondegenerate →
    ∀ (Gam : Cl → Type) [∀ c, Group (Gam c)] [∀ c, Fintype (Gam c)]
      (ρ : ∀ c, Gam c →* Module.End K V),
    (∀ c γ x y, pair (ρ c γ x) (ρ c γ y) = pair x y) →
    ∀ I : (Fin n' → K) →ₗ[K] (Cl → V), Function.Injective I →
    (∀ f : Cl → V, (∃ x, I x = f) ↔ ∀ c γ, ρ c γ (f c) = f c) →
    IsClassSum H' I pair (fun c => Fintype.card (Gam c)) →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsFullLattice K (Nab c)) →
    ∀ s : ℕ, (∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c), (s : 𝓞 K) • y ∈ Del c) →
    (∀ c, Del c ≤ Nab c) → (∀ c γ, ∀ y ∈ Del c, ρ c γ y ∈ Del c) →
    ∀ (G0 : Type) [Fintype G0] (r : G0 → Matrix (Fin n') (Fin n') K) (c : G0 → K) (G : ℕ),
    E * Pr = ∑ t, c t • r t → (∀ t, ∃ a : 𝓞 K, (a : K) = (G : K) * c t) →
    (∀ t, ∀ x ∈ valLatF I Del, (r t).mulVec x ∈ valLatF I Del) →
      Submodule.IsFullLattice K (valLatF I Nab) ∧ Submodule.IsFullLattice K (cutLat E (valLatF I Nab)) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E (valLatF I Nab)),
        ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E (valLatF I Nab)

def BoundsIVClassF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), Function.Injective I → (∀ c, 0 < g c) →
    IsClassSum H I pair g →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsFullLattice K (Nab c)) →
    ∀ s : ℕ, 0 < s → (∀ c, ∀ y ∈ Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c)) →
    ∀ DG : ℕ, 0 < DG → (∀ c, g c ∣ DG) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E (valLatF I Nab),
      (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E (valLatF I Del))) →
      Submodule.IsFullLattice K (matLat Pr (valLatF I Nab)) ∧
      jw (Eᴴ * H * E) w (matLat Pr (valLatF I Nab)) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr (valLatF I Nab)) (cutLat E (valLatF I Nab)) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K) + vw w (s : K))

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.Complement2Normaliser
section
open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

def PlOver {K : Type} [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  0 < vw w (g : K)

def PlOverCoprime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g g' : ℕ), Nat.Coprime g g' →
    ∀ w : HeightOneSpectrum (𝓞 K), ¬ (PlOver g w ∧ PlOver g' w)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.DivIntoDual
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

def DivIntoDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ) (R : Submodule (𝓞 K) (Fin D → K))
    (B : (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (F : Fin (n w) → K), P w F = ζ w * B ((ι w).mulVec ((π w).mulVec F))) →
    (∀ w, ∀ F ∈ M w, P w F = 0 ∨ 0 ≤ vw w (P w F)) →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ x ∈ R, B x ∈ Set.range (algebraMap (𝓞 K) K)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.DivIntoDualShift
section
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def smulLat {d : ℕ} (a : K) (N : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) :=
  N.map ((LinearMap.lsmul K (Fin d → K) a).restrictScalars (𝓞 K))

def IsShiftAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ) :
    Prop :=
  ∃ a : K, a ≠ 0 ∧ vw w a = -s ∧
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N)

def IsShift {d : ℕ} (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℤ) : Prop :=
  ∀ w, IsShiftAt w N N' (σ w)

def shiftIdeal (σ : HeightOneSpectrum (𝓞 K) → ℤ) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-σ w)

end Defs

def ShiftIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N N' : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K N →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (s : ℤ), IsShiftAt w N N' s →
      idx w N N' = -((d : ℤ) * s)

def MuLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K N →
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N = -(lcv X N) / d

def ShiftMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K N → Submodule.IsFullLattice K N' →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, IsShift N N' σ →
      lcv X N' = lcv X N - 2 * (d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) ∧
      (0 < d → (Function.support σ).Finite ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' =
          Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
            2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ))

def ShiftEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K N →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, (Function.support σ).Finite →
      IsShift N (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) σ ∧
      Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) ∧
      ∀ N' : Submodule (𝓞 K) (Fin d → K), IsShift N N' σ →
        N' = Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N

def ShiftPairing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ), IsShiftAt w N N' s →
    ∀ f : (Fin d → K) →ₗ[K] K, (∀ φ ∈ N, f φ = 0 ∨ s ≤ vw w (f φ)) →
      ∀ φ ∈ N', f φ = 0 ∨ 0 ≤ vw w (f φ)

def DivIntoDualShift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d D : ℕ)
    (R : Submodule (𝓞 K) (Fin D → K)) (B : (Fin d → K) →ₗ[K] (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin d → K) →ₗ[K] (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (φ : Fin d → K) (F : Fin (n w) → K),
      P w φ F = ζ w * B φ ((ι w).mulVec ((π w).mulVec F))) →
    ∀ (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
      (τ : HeightOneSpectrum (𝓞 K) → ℤ),
    (∀ w, ∀ φ ∈ N, ∀ F ∈ M w, P w φ F = 0 ∨ σ w ≤ (vw w (P w φ F) : ℝ)) →
    (∀ w, τ w ≤ ⌈σ w⌉) → IsShift N N' τ →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ φ ∈ N', ∀ x ∈ R, B φ x ∈ Set.range (algebraMap (𝓞 K) K)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HeightBoundExactNorms
section
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

section Defs

def fnorm {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℝ :=
  Formalism.HermitianLatticesTheory.cnorm (Y⁻¹.mulVec x)

def fmaj {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  ∑ i, star (Y⁻¹.mulVec x i) * Y⁻¹.mulVec y i

def pairC {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (x : Fin a → ℂ) (y : Fin D → ℂ) : ℂ :=
  ∑ i, ∑ k, x i * y k * v.embedding (B (Pi.single i 1) (Pi.single k 1))

def chainFun {m : ℕ} {C : Fin (m + 1) → Type} (Kj : ∀ j : Fin m, C j.castSucc → C j.succ) :
    ∀ i : Fin (m + 1), C 0 → C i :=
  Fin.induction (motive := fun i => C 0 → C i) id (fun j f => Kj j ∘ f)

def chainMat {R : Type} [Semiring R] {m : ℕ} {c : Fin (m + 1) → ℕ}
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) R) :
    ∀ i : Fin (m + 1), Matrix (Fin (c i)) (Fin (c 0)) R :=
  Fin.induction (motive := fun i => Matrix (Fin (c i)) (Fin (c 0)) R) 1 (fun j A => Kj j * A)

def minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

end Defs

def FnormRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K),
      fnorm (X v) (fun i => v.embedding (x i)) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ∧
      fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (y i)) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y ∧
      ((fnorm (X v) (fun i => v.embedding (x i)) ^ 2 : ℝ) : ℂ) =
        fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (x i))

def OpNormDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (a D : ℕ)
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ v, IsUnit (XM v).det) → (∀ v, IsUnit (XE v).det) →
    ∀ (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (v : InfinitePlace K) (c : ℝ), 0 ≤ c →
      (Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) v B ≤ c ↔
        ∀ (x : Fin a → ℂ) (y : Fin D → ℂ), ‖pairC v B x y‖ ≤ c * fnorm (XM v) x * fnorm (XE v) y)

def CompNormAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K,
      (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) v (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∏ j : Fin m, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j))) ∧
      (chainMat Kj (Fin.last m) ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∑ j : Fin m, Formalism.HN.htMap (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (Matrix.mulVecLin (Kj j)))

def SminLog : Prop :=
  ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (κ : ℝ) (lam : J → Ix → ℝ), 0 < κ →
    (∀ j p, 0 < lam j p) →
      0 < κ * minOver (fun p => ∏ j, lam j p) ∧
      (∀ p, κ * minOver (fun p => ∏ j, lam j p) ≤ κ * ∏ j, lam j p) ∧
      (∃ p, κ * minOver (fun p => ∏ j, lam j p) = κ * ∏ j, lam j p) ∧
      Real.log (κ * minOver (fun p => ∏ j, lam j p)) =
        Real.log κ + minOver (fun p => ∑ j, Real.log (lam j p))

def HeightBoundConstant : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
      (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin D → K)),
    (⨆ p, Qp p) = ⊤ →
    ∀ (κ : InfinitePlace K → ℝ) (lam lamL : J → Ix → InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    (∀ j p v, 0 < lamL j p v) → (∀ j p v, lamL j p v ≤ lam j p v) →
    (∀ v p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((κ v * ∏ j, lam j p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    ∀ (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
      (B : (Fin (c 0) → K) →ₗ[K] Module.Dual K (Fin D → K)),
    (∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec φ) F) → B ≠ 0 →
    ∀ (pU : InfinitePlace K → ℝ) (kU : Fin m → InfinitePlace K → ℝ),
    (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ≤ pU v) →
    (∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) →
      (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
        Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
          minOver (fun p => ∑ j, Real.log (lamL j p v))) ∧
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) B ≤
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2)) -
          (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (lamL j p v)) - meanLog κ

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.StatementJ
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def DivAssembly : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Lpass logκ Fo Eb hu hP mlam e6 eP logOm logT kk : ℝ)
    (hK eK pq : J → ℝ) (a : Pl → ℝ) (w phν nν fa eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ logκ + ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam - logκ →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, a t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then a ρ else 0) + kk * w j ρ + δ j ρ) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, ((Fintype.card J : ℝ) * (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - a t * logT) +
        (Lpass + Eb + ∑ j, eK j + e6 + eP + ∑ j, ∑ ρ, eE j ρ) +
        ∑ j, ∑ ρ, |pq j - kk| * |w j ρ| * |logOm| + ∑ j, ∑ ρ, |δ j ρ| * |logOm|

end Formalism.DivisionValues
end
end

