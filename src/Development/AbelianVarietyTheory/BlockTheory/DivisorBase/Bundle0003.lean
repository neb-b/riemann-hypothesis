module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal LinearAlgebra.Projectivization

noncomputable section

variable {d : ℕ} {X : Type} [TopologicalSpace X]

def IsProjective (A : FinHolAtlas d X) : Prop :=
  ∃ (N : ℕ) (F : X → ℙ ℂ (Fin (N + 1) → ℂ)), Function.Injective F ∧
    ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ G : X → Fin (N + 1) → ℂ,
      (∀ i, A.HoloOn W fun y => G y i) ∧
      (∀ y ∈ W, ∃ h : G y ≠ 0, F y = Projectivization.mk ℂ (G y) h) ∧
      ∀ j, x ∈ (A.chart j).source → ∀ v : Fin d → ℂ,
        fderiv ℂ (G ∘ (A.chart j).symm) (A.chart j x) v ∈ Submodule.span ℂ {G x} → v = 0

def IsIrreducibleAnalytic (A : FinHolAtlas d X) (Z : Set X) : Prop :=
  A.IsAnalyticSubset Z ∧ Z.Nonempty ∧
    ∀ Z₁ Z₂, A.IsAnalyticSubset Z₁ → A.IsAnalyticSubset Z₂ → Z = Z₁ ∪ Z₂ → Z = Z₁ ∨ Z = Z₂

def IsIrreducibleComponent (A : FinHolAtlas d X) (S C : Set X) : Prop :=
  Maximal (fun C' => IsIrreducibleAnalytic A C' ∧ C' ⊆ S) C

def padZero (n d : ℕ) (z : Fin n → ℂ) : Fin d → ℂ :=
  fun k => if h : (k : ℕ) < n then z ⟨k, h⟩ else 0

def IsStraightening (A : FinHolAtlas d X) (Z : Set X) (n : ℕ)
    (ψ : OpenPartialHomeomorph X (Fin d → ℂ)) : Prop :=
  n ≤ d ∧ IsCompatChart A ψ ∧
    Z ∩ ψ.source = {y ∈ ψ.source | ∀ k : Fin d, n ≤ (k : ℕ) → ψ y k = 0}

def regularLocus (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) : Set X :=
  {x ∈ Z | ∃ ψ, IsStraightening A Z n ψ ∧ x ∈ ψ.source}

def param (n : ℕ) (ψ : OpenPartialHomeomorph X (Fin d → ℂ)) (z : Fin n → ℂ) : X :=
  ψ.symm (padZero n d z)

def paramDens (n : ℕ) (Φ : LocPot X) (ψ : OpenPartialHomeomorph X (Fin d → ℂ))
    (z : Fin n → ℂ) : ℝ :=
  maDens (fun _ z' => Φ.φ (param n ψ z) (param n ψ z')) z

def IsPieceFamily (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) (S : Set X) {k : ℕ}
    (ψ : Fin k → OpenPartialHomeomorph X (Fin d → ℂ)) (B : Fin k → Set (Fin n → ℂ)) : Prop :=
  (∀ j, IsStraightening A Z n (ψ j)) ∧ (∀ j, MeasurableSet (B j)) ∧
    (∀ j, ∀ z ∈ B j, padZero n d z ∈ (ψ j).target ∧ param n (ψ j) z ∈ S) ∧
    Pairwise fun i j => Disjoint (param n (ψ i) '' B i) (param n (ψ j) '' B j)

def regIntegral (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) (Φ : LocPot X) (S : Set X)
    (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (ψ : Fin k → OpenPartialHomeomorph X (Fin d → ℂ)) (B : Fin k → Set (Fin n → ℂ))
    (_ : IsPieceFamily A Z n S ψ B),
    ∑ j, ∫⁻ z in B j, f (param n (ψ j) z) * ‖paramDens n Φ (ψ j) z‖ₑ

def normSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  ‖s y y‖ * Real.exp (-L.φ y y)


open scoped Classical in
def absLogNorm (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ≥0∞ :=
  if s y y = 0 then ∞ else ENNReal.ofReal |logNormSec L s y|

def boundary {m : ℕ} (σ : Fin m → X → X → ℂ) : Set X :=
  {y | ∃ i, σ i y y = 0}

def rFun (L : LocPot X) (σ : X → X → ℂ) (y : X) : ℝ :=
  Real.exp 1 - 2 * logNormSec L σ y

def pFun {m : ℕ} (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ) (y : X) : ℝ :=
  -c * ∑ i, Real.log (rFun (Λ i) (σ i) y)

def poincarePot {m : ℕ} (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ)
    (c : ℝ) : LocPot X :=
  α + LocPot.ofFun fun y => pFun Λ σ c y / 2

def FormBoundedBy (A : FinHolAtlas d X) (α L : LocPot X) (K : ℝ) : Prop :=
  IsPsh A (α.rsmul K + L) ∧ IsPsh A (α.rsmul K + L.rsmul (-1))

def IsAdmissibleConst {m : ℕ} (A : FinHolAtlas d X) (α : LocPot X) (Λ : Fin m → LocPot X)
    (c : ℝ) : Prop :=
  0 < c ∧ ∃ K : Fin m → ℝ, (∀ i, 0 ≤ K i ∧ FormBoundedBy A α (Λ i) (K i)) ∧
    c * ∑ i, K i ≤ Real.exp 1 / 2

def IsBoundarySetting {m : ℕ} (A : FinHolAtlas d X) (α : LocPot X) (Λ : Fin m → LocPot X)
    (σ : Fin m → X → X → ℂ) (c : ℝ) : Prop :=
  IsPotential A α ∧ IsPosPot A α ∧
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧
      interior {y | σ i y y = 0} = ∅ ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1) ∧
    IsAdmissibleConst A α Λ c

end

end GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
section
open Matrix MeasureTheory
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

abbrev Fl (g : ℕ) : Type := Fin g ⊕ Fin g → ℝ

def riem {g : ℕ} (x y : Fl g) : ℝ :=
  ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i))

def symp (g : ℕ) : Fl g [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := riem (v 0) (v 1)
  map_update_add' := by
    intro inst v i x y
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, add_mul, mul_add, Finset.sum_add_distrib] <;> ring
  map_update_smul' := by
    intro inst v i c x
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, ← Finset.sum_sub_distrib, Finset.mul_sum] <;>
      exact Finset.sum_congr rfl fun _ _ => by ring
  cont := by
    unfold riem
    fun_prop
  map_eq_zero_of_eq' := by
    intro v i j h hij
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    simp only [riem, h01]
    exact Finset.sum_eq_zero fun _ _ => by ring

def stdLat (g : ℕ) : Submodule ℤ (Fl g) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g ⊕ Fin g)))

def wedgePow {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (α : T [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) (v : Fin k × Fin 2 → T) : ℝ :=
  (1 / 2 ^ k) * ∑ σ : Equiv.Perm (Fin k × Fin 2),
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, α ![v (σ (i, 0)), v (σ (i, 1))]

def per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) : Fin g → ℂ :=
  (fun i => (x (Sum.inl i) : ℂ)) ᵥ* τ + fun i => (x (Sum.inr i) : ℂ)

def flatOf {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : Fl g :=
  Sum.elim ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹)
    ((fun i => (z i).re) - ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.re)

abbrev Sp (g : ℕ) : Type := Matrix.symplecticGroup (Fin g) ℝ

section Family

abbrev Pt (E : Type) (g : ℕ) : Type := E × (Fin g → ℂ)

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g : ℕ}

abbrev Form2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℕ) : Type :=
  Pt E g [⋀^Fin 2]→L[ℝ] ℝ

def IsPeriodMap (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  IsOpen B ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) ∧ ∀ b ∈ B, IsSiegel (τ b)

def cov (B : Set E) (g : ℕ) : Set (Pt E g) := B ×ˢ Set.univ

def flat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Fl g := flatOf (τ P.1) P.2

def dflat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Pt E g →L[ℝ] Fl g :=
  fderiv ℝ (flat τ) P

def om0 (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Form2 E g :=
  (symp g).compContinuousLinearMap (dflat τ P)

def pull (f : Pt E g → Pt E' g) (α : Pt E' g → Form2 E' g) (P : Pt E g) : Form2 E g :=
  (α (f P)).compContinuousLinearMap (fderiv ℝ f P)

def transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) : Pt E g :=
  (P.1, P.2 + per (τ P.1) x)

def ddc (u : Pt E g → ℝ) (P v w : Pt E g) : ℝ :=
  (1 / (4 * π)) * (fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • v)) P w -
    fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • w)) P v)

def IsFactor (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  (∀ l ∈ M, DifferentiableOn ℂ (j l) (cov B g) ∧ ∀ P ∈ cov B g, j l P ≠ 0) ∧
  ∀ l ∈ M, ∀ l' ∈ M, ∀ P ∈ cov B g, j (l + l') P = j l (transl τ l' P) * j l' P

def IsMetric (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h (cov B g) ∧ (∀ P ∈ cov B g, 0 < h P) ∧
  ∀ l ∈ M, ∀ P ∈ cov B g, h (transl τ l P) * ‖j l P‖ ^ 2 = h P

def ChernIsFlat (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) : Prop :=
  ∀ P ∈ cov B g, ∀ v w : Pt E g, -ddc (fun Q => Real.log (h Q)) P v w = om0 τ P ![v, w]

def InducesPolarisation (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  ∀ b ∈ B, ∃ f : Fl g → (Fin g → ℂ) → ℂ,
    (∀ l ∈ M, Differentiable ℂ (f l) ∧ ∀ z, j l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧
    ∀ l ∈ M, ∀ l' ∈ M, ∀ z,
      f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = (riem l l' : ℂ)

end Family

def symMat (g : ℕ) : Submodule ℂ (Fin g → Fin g → ℂ) where
  carrier := {A | ∀ i j, A i j = A j i}
  add_mem' := fun {A B} hA hB i j => by simp [hA i j, hB i j]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c A hA i j => by simp [hA i j]

def tauU {g : ℕ} (s : symMat g) : Matrix (Fin g) (Fin g) ℂ := Matrix.of s.1

def siegel (g : ℕ) : Set (symMat g) := {s | IsSiegel (tauU s)}

def symPart {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : symMat g :=
  ⟨fun i j => (A i j + A j i) / 2, fun i j => by simp only [add_comm]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
end
end

