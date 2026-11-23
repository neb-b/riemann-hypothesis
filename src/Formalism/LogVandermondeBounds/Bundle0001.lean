module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LogVandermondeBounds.FinrankFiberSumZero
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

def pair (f x : Fin r → k) : k := ∑ i, f i * x i

def opU (ψ : (Fin r → k) → R) (f : Fin r → k) : R :=
  ∑ x ∈ univ.filter (fun x => pair f x = 1), ψ x

def opD (φ : (Fin r → k) → R) (x : Fin r → k) : R :=
  ∑ f ∈ univ.filter (fun f => pair f x = 1), φ f

def diaP (c : kˣ) (φ : (Fin r → k) → R) (f : Fin r → k) : R := φ ((c : k) • f)

def diaV (c : kˣ) (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ψ (((c⁻¹ : kˣ) : k) • x)

def nmP (φ : (Fin r → k) → R) (f : Fin r → k) : R := ∑ c : kˣ, diaP c φ f

def nmV (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ∑ c : kˣ, diaV c ψ x

def trV (ψ : (Fin r → k) → R) : R := ∑ x ∈ univ.filter (fun x => x ≠ 0), ψ x

def trP (φ : (Fin r → k) → R) : R := ∑ f ∈ univ.filter (fun f => f ≠ 0), φ f

end Ops

def ramSub (ι H X K : Type) [DecidableEq ι] [Group H] [Fintype H] [MulAction (ι → H) X] [Field K] :
    Submodule K (X → K) where
  carrier := {φ | ∀ (v : ι) (x : X), ∑ c : H, φ ((Pi.mulSingle v c : ι → H) • x) = 0}
  add_mem' := fun {a b} ha hb v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    have h2 : ∑ c : H, b ((Pi.mulSingle v c : ι → H) • x) = 0 := hb v x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [h1, h2, add_zero]
  zero_mem' := fun v x => by simp
  smul_mem' := fun s a ha v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h1, mul_zero]

def FinrankFiberSumZero : Prop :=
  ∀ (ι H X K : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] [Field K],
    (∀ (g : ι → H) (x : X), g • x = x → g = 1) →
    Module.finrank K (ramSub ι H X K) * Fintype.card H ^ Fintype.card ι =
      Fintype.card X * (Fintype.card H - 1) ^ Fintype.card ι

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

-- bundled from Formalism.LogVandermondeBounds.LogRatioLowerBound
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)

noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

noncomputable def zetaR (M : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M

noncomputable def rowPar (k : ℕ) (v b : ℕ → ℝ) : ℕ → ℝ := fun i => if i < k - 1 then v i else - b (i - (k - 1))

def PlaceData (x Δ a B : ℝ) (k m : ℕ) (u v b w : ℕ → ℝ) : Prop :=
  (∀ i, i < k - 1 → 0 ≤ v i ∧ v i ≤ k * (4 * Δ)) ∧
  (∀ i, i + 1 < k - 1 → v i - v (i + 1) = 4 * Δ) ∧
  (∀ i, i < k - 1 → v i < u i ∧ u (i + 1) < v i) ∧
  (- b 0 < u (k - 1)) ∧
  ((u 0 ≤ 2 * a ∧ - a ≤ u (k - 1)) ∨
    (k * (4 * Δ) ≤ u 0 - v 0 ∧ u 0 - v 0 ≤ 2 * k * (4 * Δ) ∧ u (k - 1) = v (k - 2) - 1 / 2)) ∧
  (∀ j, j < m → b j < w j ∧ |w j - b j| ≤ b j / x) ∧
  (∀ j, j + 1 < m → w j < b (j + 1) ∧ 1 ≤ b (j + 1) - b j) ∧
  k * (4 * Δ) ≤ b 0 / x ∧ w (m - 1) ≤ 2 * B

def LogRatioLowerBound : Prop :=
  ∀ (ε C₀ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (f m k : ℕ) (vE Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ)
      (Dstar dstar massk massr Isig Ipi : ℝ) (Lval : ℕ → ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ vE → Real.log vE ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    (∀ ρ, ρ < f → PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ)) →
    0 < massk → 0 < massr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi) →
    (hD : (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) ≤ Dstar) →
    (hd : dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k) →
    (∑ j ∈ range m, (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j * vE / Real.pi))
        + m * (Real.log g₁ + Real.log g₂) - C * (L + (m : ℝ) ^ 2 * L / k)
      ≤ (1 / ((f : ℝ) * k)) * Real.log (Dstar / dstar)

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def CardGeneralLinear : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * (n - 1) / 2) * (Fintype.card F : ℝ) ^ (n * (n + 1) / 2) *
        ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1))

def CardUnitriangular : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    Nat.card {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} =
      Fintype.card F ^ (n * (n - 1) / 2)

def EulerProductBounds : Prop :=
  ∀ (q : ℝ), 3 ≤ q → ∀ n : ℕ,
    1 / 2 ≤ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ∧ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ≤ 1

def CardStabilizerVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (v : Fin n → F), v ≠ 0 →
    Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} *
      (Fintype.card F ^ n - 1) = Fintype.card (GL (Fin n) F)

def PrimeOrderFinrank : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n g : ℕ) (A : Matrix (Fin n) (Fin n) K),
    g.Prime → A ^ g = 1 → A ≠ 1 → g - 1 ≤ Module.finrank ℚ K * n

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.MultinomialPowerBound
section
namespace Formalism.LogVandermondeBounds.flipTwoThree

open Finset

def Interlace {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : Prop :=
  Antitone lam ∧ ∀ i : Fin n, lam i.succ ≤ nu i ∧ nu i ≤ lam i.castSucc

def B0 {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : ℤ := ∑ i, (nu i - lam i.succ)

def len {n : ℕ} (lam : Fin (n + 1) → ℤ) (i : Fin n) : ℤ := lam i.castSucc - lam i.succ

noncomputable def hookF {N : ℕ} (nu : Fin N → ℕ) : ℝ :=
  (∏ i : Fin N, ((nu i + N - 1 - i : ℕ).factorial : ℝ)) /
    ∏ i : Fin N, ∏ j ∈ univ.filter (fun j => i < j), (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ)

end Formalism.LogVandermondeBounds.flipTwoThree
end

