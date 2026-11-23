module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Formalism.ThetaSupremumBounds.StatementE

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
section
open Matrix Complex Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram

open GlobalTheory.HermFrame

variable {n a g : ℕ}

def polydisc (n : ℕ) (ρ : ℝ) : Set (Fin n → ℂ) := {z | ∀ k, ‖z k‖ < ρ}

def punctured (ha : a ≤ n) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {z | z ∈ polydisc n ρ ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}

def tlog (w : ℂ) : ℝ := -Real.log ‖w‖ / (2 * Real.pi)

structure IsPeriodChart (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Prop where

  rk_le : rk ≤ g

  holo : ∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (polydisc n 1)

  symm : ∀ z ∈ polydisc n 1, (τ₀ z).IsSymm

  psd : ∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef

  supp : ∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0

  toric : (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix
    (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef

  abelian : ∀ z ∈ polydisc n 1, (((τ₀ z).map Complex.im).submatrix
    (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef

def period (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (z : Fin n → ℂ) (L : Fin a → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  τ₀ z + ∑ i, (L i / (2 * Real.pi * I)) • (B i).map (Int.cast : ℤ → ℂ)

def imPeriod (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ₀ z).map Complex.im + ∑ i, tlog (z (Fin.castLE ha i)) • (B i).map (Int.cast : ℤ → ℝ)

def hodgeGram (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (imPeriod ha τ₀ B z).map Complex.ofReal

def poincareGram (a : ℕ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun k =>
    ((if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2 : ℝ) : ℂ)

def BoundsOn (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ρ c C : ℝ) : Prop :=
  (∀ z ∈ punctured ha ρ, (imPeriod ha τ₀ B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) ∧
  (∀ z ∈ punctured ha ρ,
    ((C * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ)
      - imPeriod ha τ₀ B z).PosSemidef) ∧
  OneFormBound (punctured ha ρ) (fun _ => 1) (poincareGram a) (conn (hodgeGram ha τ₀ B)) C ∧
  TwoFormBound (punctured ha ρ) (hodgeGram ha τ₀ B) (poincareGram a) (curv (hodgeGram ha τ₀ B)) C

def HodgeChartBounds : Prop :=
  ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B →
    ∃ ρ c C : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 < c ∧ BoundsOn ha τ₀ B ρ c C


open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog w :=
  div_pos (neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr h0) h1)) (by positivity)


open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (L : Fin a → ℂ)
    (hL : ∀ i, exp (L i) = z (Fin.castLE ha i)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B z L).map Complex.im = _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B z := by
  ext j k
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod, Matrix.map_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.add_im, Complex.im_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hL i, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog, Complex.norm_exp, Real.log_exp]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Complex.mul_im, Complex.div_re, Complex.div_im]
  simp [Complex.normSq_apply]
  field_simp


open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.conn_hodgeGram {rk : ℕ} (ha : a ≤ n) {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin a → Matrix (Fin g) (Fin g) ℤ} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B) {z : Fin n → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) (ξ : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.conn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ =
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z)⁻¹ * _root_.GlobalTheory.HermFrame.mdel (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ := by
  apply _root_.GlobalTheory.HermFrame.conn_eq_of_isSymm
  have hnear : ∀ᶠ x in 𝓝 z, x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1 :=
    Filter.eventually_all.2 fun k =>
      (continuous_apply k).norm.continuousAt.eventually_lt continuousAt_const (hz k)
  filter_upwards [hnear] with x hx
  have hB : ∀ i, ((B i).map (Int.cast : ℤ → ℝ))ᵀ = (B i).map (Int.cast : ℤ → ℝ) := fun i => by
    have := (h.psd i).isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hτ : ((τ₀ x).map Complex.im)ᵀ = (τ₀ x).map Complex.im := by
    rw [← Matrix.transpose_map, (h.symm x hx).eq]
  have hI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B x).IsSymm := by
    unfold Matrix.IsSymm _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod
    rw [Matrix.transpose_add, Matrix.transpose_sum, hτ]
    simp only [Matrix.transpose_smul, hB]
  exact hI.map _

end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TaylorCoefficientForms
section
open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms

open Formalism.DimensionVariation (mono mfact nsq liftBlock)

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def dirDeriv (v : E) (F : E → ℂ) : E → ℂ := fun z => fderiv ℂ F z v

def monoDeriv (v : κ → E) (e : κ → ℕ) (F : E → ℂ) : E → ℂ :=
  (univ : Finset κ).toList.foldr (fun x G => (dirDeriv (v x))^[e x] G) F


open Classical in
def coordVec (x : κ) : κ → ℂ := Pi.single x 1

def taylorCoeff (F : (κ → ℂ) → ℂ) (e : κ → ℕ) : ℂ :=
  monoDeriv coordVec e F 0 / (mfact e : ℂ)

end Calculus

def lineForm (ξ D D' : ℂ) : ℂ := 2 * (‖ξ‖ : ℂ) * (D * conj D')

def period (ξ D : ℂ) : ℝ := 1 / (π * (lineForm ξ D D).re)

section OnePlace

variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B] {n₀ n₁ : ℕ}

end OnePlace

section AllPlaces

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}


end AllPlaces

end GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorCoordinateForms
section
open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms

def dirDeriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) (F : V → ℂ) : V → ℂ :=
  fun z => fderiv ℂ F z v

def wordDeriv {κ V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : κ → V) (w : List κ)
    (F : V → ℂ) : V → ℂ :=
  w.foldr (fun x G => dirDeriv (v x) G) F

def IsSpelling {κ : Type} [DecidableEq κ] (w : (κ → ℕ) → List κ) : Prop :=
  ∀ e x, (w e).count x = e x

def lineForm (a : ℝ) (D D' : ℂ) : ℂ := 2 * (a : ℂ) * (D * conj D')

def omega (a : ℝ) (D : ℂ) : ℝ := 1 / (π * (lineForm a D D).re)

section OnePlace

variable {X X' : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [FiniteDimensional ℂ X'] {n₀ n₁ : ℕ}

end OnePlace

section Places

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X X' : Pl → Type}
  [∀ τ, NormedAddCommGroup (X τ)] [∀ τ, InnerProductSpace ℂ (X τ)] [∀ τ, FiniteDimensional ℂ (X τ)]
  [∀ τ, NormedAddCommGroup (X' τ)] [∀ τ, InnerProductSpace ℂ (X' τ)] [∀ τ, FiniteDimensional ℂ (X' τ)]
  {n₀ n₁ : ℕ}

end Places

def coordVec {κ : Type} [DecidableEq κ] (p : κ) : κ → ℂ := Pi.single p 1

end GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms
end
end

