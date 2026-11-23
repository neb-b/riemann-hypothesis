module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.EulerProductSatake
section
open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors

noncomputable section

abbrev Place (K : Type) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

def normAt {K : Type} [Field K] [NumberField K] (w : Place K) : ℝ :=
  (Ideal.absNorm w.asIdeal : ℝ)

section Euler

variable {K : Type} [Field K] [NumberField K] {ι : Type}

def localFactor (I : Finset ι) (x : Place K → ι → ℂ) (w : Place K) : ℂ :=
  ∏ i ∈ I, (1 - x w i)⁻¹

def eulerProd (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : ℂ :=
  ∏' w : {w : Place K // w ∉ T}, localFactor I x w.1

end Euler

def SatakeBound {E : Type} [Field E] [NumberField E] (T : Set (Place E)) (r : ℕ) (s : ℝ)
    (x : Place E → Fin r → ℂ) : Prop :=
  ∀ w, w ∉ T → ∀ i, ‖x w i‖ ≤ normAt w ^ (((r : ℝ) - 1) / 2 - s)

def twistTerm {F : Type} [Field F] [NumberField F] (ω : Place F → ℂ) (v : Place F) (i : ℕ) : ℂ :=
  ω v ^ i * ((normAt v : ℂ) ^ i)⁻¹

def dPart {F : Type} [Field F] [NumberField F] (S : Set (Place F)) (ω : Place F → ℂ)
    (r t : ℕ) : ℂ :=
  eulerProd S (Finset.Icc (t + 1) (r + t)) (twistTerm ω)

def placesOver {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (S : Set (Place F)) : Set (Place E) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}


open Classical in
def quadSign {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (v : Place F) : ℂ :=
  by
    classical
    exact if (placesOver E ({v} : Set (Place F))).ncard = 2 then 1
      else if (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime then -1 else 0

end

end GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
section
open MeasureTheory Set

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral

variable {X : Type} [MeasurableSpace X]

noncomputable def flatIntegrand (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) (x : X) : ℂ :=
  f x * ((a x : ℝ) : ℂ) ^ (s - s₀)

noncomputable def flatZeta (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) : ℂ :=
  ∫ x, flatIntegrand f a s₀ s x ∂μ

def ConvergesAbsLocUnifOn (μ : Measure X) (F : ℂ → X → ℂ) (D : Set ℂ) : Prop :=
  (∀ s ∈ D, Integrable (F s) μ) ∧
    ∀ s ∈ D, ∃ U ∈ nhdsWithin s D, ∃ g : X → ℝ, Integrable g μ ∧
      ∀ s' ∈ U, ∀ x, ‖F s' x‖ ≤ g x

def FlatZetaHolomorphic : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s₁ : ℂ),
    Measurable a → (∀ x, 0 < a x) → (∀ x, a x ≤ 1) →
    Integrable (flatIntegrand f a s₀ s₁) μ →
      ConvergesAbsLocUnifOn μ (flatIntegrand f a s₀) {s | s₁.re ≤ s.re} ∧
      DifferentiableOn ℂ (flatZeta μ f a s₀) {s | s₁.re < s.re} ∧
      ContinuousOn (flatZeta μ f a s₀) {s | s₁.re ≤ s.re}


omit [MeasurableSpace X] in
theorem flatIntegrand_self (f : X → ℂ) (a : X → ℝ) (s₀ : ℂ) : flatIntegrand f a s₀ s₀ = f := by
  funext x
  simp [flatIntegrand]


omit [MeasurableSpace X] in
theorem norm_flatIntegrand (f : X → ℂ) {a : X → ℝ} (s₀ s : ℂ) {x : X} (hx : 0 < a x) :
    ‖flatIntegrand f a s₀ s x‖ = ‖f x‖ * a x ^ (s.re - s₀.re) := by
  rw [flatIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re]

end GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
section
noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup

section Defs

variable (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))]

abbrev Int : Subring F := (Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ))).integer

def upperBorel (r : ℕ) (k : Type) [CommRing k] : Subgroup (GL (Fin r) k) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) k).BlockTriangular id}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun {g} hg => by
    have := g.invertible
    have h := Matrix.blockTriangular_inv_of_blockTriangular hg
    simpa [Matrix.coe_units_inv] using h

def maxId : Ideal (Int F) where
  carrier := {x | Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ))}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simpa using Valuation.map_add_lt _ ha hb
  smul_mem' := fun c x hx => by
    have hc : Valued.v (c : F) ≤ (1 : WithZero (Multiplicative ℤ)) := c.2
    have hx' : Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ)) := hx
    show Valued.v ((c * x : Int F) : F) < (1 : WithZero (Multiplicative ℤ))
    rw [Subring.coe_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx'

def iwahoriInt (r : ℕ) : Subgroup (GL (Fin r) (Int F)) :=
  (upperBorel r (Int F ⧸ maxId F)).comap
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)))

def iwahori (r : ℕ) : Subgroup (GL (Fin r) F) :=
  (iwahoriInt F r).map (Matrix.GeneralLinearGroup.map (Int F).subtype)

variable {F}

def diagPow {r : ℕ} (ϖ : F) (a : Fin r → ℤ) : Matrix (Fin r) (Fin r) F :=
  Matrix.diagonal fun i => ϖ ^ a i

def iwahoriDoubleCoset {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : Set (Matrix (Fin r) (Fin r) F) :=
  {g | ∃ i₁ ∈ iwahori F r, ∃ i₂ ∈ iwahori F r,
    g = (i₁ : Matrix (Fin r) (Fin r) F) * t * (i₂ : Matrix (Fin r) (Fin r) F)}

end Defs

def IwahoriEigenvalues : Prop :=
  ∀ (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] [CompleteSpace F]
    (ϖ : F), Valued.v ϖ = WithZero.exp (-1 : ℤ) →
    ∀ (r : ℕ) (a : Fin r → ℤ), StrictAnti a →
    ∀ g ∈ iwahoriDoubleCoset (diagPow ϖ a),
      (∃ x : Fin r → F, Function.Injective x ∧
        g.charpoly = ∏ i, (X - C (x i)) ∧
        ∀ i, Valued.v (x i) = WithZero.exp (-(a i))) ∧
      g.charpoly.Separable

theorem mem_iwahoriInt_iff (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] (r : ℕ)
    (g : GL (Fin r) (Int F)) :
    g ∈ iwahoriInt F r ↔ ∀ i j : Fin r, j < i →
      Valued.v (((g : Matrix (Fin r) (Fin r) (Int F)) i j : Int F) : F)
        < (1 : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro h i j hij
    have := h (i := i) (j := j) hij
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · intro h i j hij
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h i j hij)

theorem self_mem_iwahoriDoubleCoset {F : Type} [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : t ∈ iwahoriDoubleCoset t :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup
end
end

