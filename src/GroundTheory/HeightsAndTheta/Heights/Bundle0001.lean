module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.CovolumeGram
section
namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix Module

theorem covolume_eq_sqrt_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L = Real.sqrt (gram ℝ fun i ↦ (b i : V)).det := by
  have hcard : Fintype.card ι = finrank ℝ V := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hcard).symm
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one,
    mul_one, gram_eq_conjTranspose_mul o, det_mul, det_conjTranspose, star_trivial,
    ← sq, Real.sqrt_sq_eq_abs, Basis.det_apply]
  congr 2

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KernelsLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding Matrix Real
open scoped ComplexOrder nonZeroDivisors

noncomputable section

def genIndex {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : ℝ :=
  (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

variable {K : Type*} [Field K]

def embVec (σ : K →+* ℂ) {n : ℕ} (v : Fin n → K) : Fin n → ℂ := fun j => σ (v j)

def gramAt {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} (u : ι → Fin n → K) :
    Matrix ι ι ℂ :=
  fun a b => star (embVec σ (u a)) ⬝ᵥ (h *ᵥ embVec σ (u b))

variable [NumberField K]

structure HermLattice (K : Type*) [Field K] [NumberField K] (n : ℕ) where

  lattice : Submodule (𝓞 K) (Fin n → K)
  fg : lattice.FG
  span_eq : Submodule.span K (lattice : Set (Fin n → K)) = ⊤

  metric : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ
  posDef : ∀ σ, (metric σ).PosDef
  conj : ∀ σ, metric (conjugate σ) = (metric σ).map (starRingEnd ℂ)

def subDegree {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (h : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) : ℝ :=
  log (genIndex (L ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup) -
    1 / 2 * ∑ σ : K →+* ℂ, log (gramAt (h σ) σ u).det.re


variable (K) in
def normalise (x : ℝ) : ℝ := x / Module.finrank ℚ K

namespace HermLattice

variable {n : ℕ}

def degree (F : HermLattice K n) : ℝ :=
  subDegree F.lattice F.metric (fun j : Fin n => (Pi.single j 1 : Fin n → K))

def slope (F : HermLattice K n) : ℝ := normalise (K := K) F.degree / n

def lineDegree (F : HermLattice K n) (K' : Type*) [Field K'] [NumberField K'] [Algebra K K']
    (v : Fin n → K') : ℝ :=
  normalise (K := K') (subDegree
    (Submodule.span (𝓞 K') ((fun w : Fin n → K => fun j => algebraMap K K' (w j)) '' F.lattice))
    (fun σ' => F.metric (σ'.comp (algebraMap K K'))) (fun _ : Fin 1 => v))

end HermLattice

def idealLattice {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.pi Set.univ fun x => (a x : Submodule (𝓞 K) K)

def diagMetric {n : ℕ} (d : (K →+* ℂ) → Fin n → ℝ) : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => Matrix.diagonal fun x => (d σ x : ℂ)

def LineOfLargeDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ), 1 ≤ i → ∀ (F : HermLattice K i) (ε : ℝ), 0 < ε →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
      v ≠ 0 ∧ F.slope - 1 / 2 * log i - ε ≤ F.lineDegree K' v

def HermLattice.standard (K : Type*) [Field K] [NumberField K] (n : ℕ) : HermLattice K n where
  lattice := Submodule.span (𝓞 K) (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    rw [Submodule.span_span_of_tower]
    have h : (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K)) =
        Set.range (Pi.basisFun K (Fin n)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun K (Fin n)).span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)

def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

def SymplecticReduction.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      ρsq ≤ 2 * g ∧
      ∃ P ∈ symplecticGroup (Fin g) ℤ,
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁.det ≤
          ρsq * (2 * g) ^ (g - 1)

def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)

def SiegelCoordinates.Statement : Prop :=
  ∀ g : ℕ,
    (∀ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm → Y.PosDef →
      siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef) ∧
    ∀ G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
      ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
        XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2

def GaussianSum.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) →
    ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g

def periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (↑) + Complex.I • Y.map (↑)

def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (π * Complex.I *
        ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
          (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
      2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def thetaNorm {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ))‖ *
    exp (-π * qf Y u₁)

structure IsReducedImaginaryPart {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) :
    Prop where
  pos : 0 < ρ
  sq_le : ρ ^ 2 ≤ 2 * g
  first : Y⁻¹ 0 0 = ρ ^ 2
  min : ∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)
  det_le : Y⁻¹.det ≤ ρ ^ 2 * (2 * g) ^ (g - 1)

def ThetaBound.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) [NeZero g] (X Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ)
    (a b : Fin g → ℝ), X.IsSymm → Y.PosDef → IsReducedImaginaryPart Y ρ →
    (∀ i, ∃ m : ℤ, a i = m / 2) → (∀ i, ∃ m : ℤ, b i = m / 2) →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) ∧
    ∀ u₁ u₂ : Fin g → ℝ,
      thetaNorm X Y a b u₁ u₂ ≤ ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
        exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2 +
          (g * log (1 + 1 / ρ) + C * g * log (2 * g)))

def finMean {S : Type*} [Fintype S] (f : S → ℝ) : ℝ := (∑ s, f s) / Fintype.card S

def WeakMatrixArithmetic.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) [NeZero g] (S : Type) [Fintype S] [Nonempty S] (ρ : S → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ √(2 * g)) → 0 ≤ Φ →
      finMean (fun s => π / 96 * (ρ s ^ 2)⁻¹ - (g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g))) ≤ Φ →
      finMean (fun s => (ρ s ^ 2)⁻¹) ≤ C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g)) ≤
        C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => posLog (1 / ρ s)) ≤ 1 / 2 * log (1 + finMean (fun s => (ρ s ^ 2)⁻¹))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KernelsRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Real

noncomputable section

def alternant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) : MvPolynomial ι ℚ :=
  (Matrix.of fun i i' : ι => (X i : MvPolynomial ι ℚ) ^ e i').det

def antisym {ι : Type*} [Fintype ι] [DecidableEq ι] (H : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  ∑ w : Equiv.Perm ι, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w H

def frobDim {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ((∑ a, la a).factorial : ℚ) *
      (∏ a : Fin r, ∏ b : Fin r,
        if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1) /
    ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ)

def FrobeniusRectangleBound.Statement : Prop :=
  ∀ (r s : ℕ) (ν : Fin r → ℕ), Antitone ν →
    frobDim (fun a => s + ν a) ≤
      ((r * s + ∑ a, ν a).choose (∑ a, ν a) : ℚ) * frobDim (fun _ : Fin r => s) * frobDim ν

abbrev RootPoly (f j k : ℕ) : Type := MvPolynomial (Fin f × (Fin j ⊕ Fin k)) ℝ

variable (f j k : ℕ)

def flagDim : ℕ := f * ((j + k) * (j + k - 1) / 2)

def rootPsum (m : ℕ) (τ : Fin f) : RootPoly f j k := ∑ i, X (τ, i) ^ m

def lieClass (m : ℕ) : Fin f × Bool → RootPoly f j k
  | (τ, false) => ∑ a : Fin j, X (τ, Sum.inl a) ^ m
  | (τ, true) => (-1) ^ m * ∑ b : Fin k, X (τ, Sum.inr b) ^ m

def vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) : R :=
  (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det

def fibre : RootPoly f j k :=
  ∏ τ : Fin f, if k ≤ j then
      vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Sum.inl a) : RootPoly f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Sum.inl a) : RootPoly f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k))

structure IsFlagIntegral (I : RootPoly f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : RootPoly f j k), 1 ≤ m → m ≤ flagDim f j k →
    G.IsHomogeneous (flagDim f j k - m) → I (rootPsum f j k m τ * G) = 0
  ne_zero : ∃ G : RootPoly f j k, G.IsHomogeneous (flagDim f j k) ∧ I G ≠ 0

def IsPowerSumDecomposition (F : RootPoly f j k) (Q : Fin f → ℕ → RootPoly f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (flagDim f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), rootPsum f j k m τ * Q τ m

def restAt (I : RootPoly f j k →ₗ[ℝ] ℝ) (vol : ℝ) (φ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → RootPoly f j k) (p : ℕ) : ℝ :=
  log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ,
    (((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m))

end

end GroundTheory.Heights₂.Heights
end

