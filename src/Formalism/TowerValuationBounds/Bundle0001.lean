module

public import Mathlib

@[expose] public section

-- bundled from Formalism.TowerValuationBounds.HermitianSumValuationBound
section
noncomputable section

namespace Formalism.ValuationGridEstimates

open Finset

def AbsValuationSumBound : Prop :=
  ∀ (W E : Type) [Fintype E] (lam val δ : W → ℝ) (absx : E → ℝ) (Wx : Finset W) (Bδ : ℝ),
    (∀ w, 0 ≤ lam w) → (∀ w, w ∉ Wx → val w = 0) →
    ∑ w ∈ Wx, lam w * val w = (∑ σ, Real.log (absx σ)) / Fintype.card E →
    (∑ w ∈ Wx, lam w * |val w| =
        (∑ σ, Real.log (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    (∑ w ∈ Wx, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    ((∀ w, 0 ≤ δ w) → (∀ w, -(3 * δ w) ≤ val w) → (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
      ∀ F : Finset W, ∑ w ∈ F, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 6 * Bδ)

def TowerProductFormula : Prop :=
  ∀ (K : Type) [Field K] (L : ℤ → K) (c u : ℕ → ℕ → K) (p q : ℕ) (e : ℤ),
    (∀ k : ℕ, 1 ≤ k → k ≤ q → L (e + k) ≠ 0) →
    (∀ j, j < q → c 0 j * L (e + j + 1) = u 0 j * c 0 (j + 1)) →
    (∀ i, i < p → c i q = u i q * L (e - i + q) * c (i + 1) q) →
    c 0 0 = ((∏ j ∈ range q, u 0 j) * ∏ i ∈ range p, u i q) * c p q *
      (∏ k ∈ Icc 1 p, L (e + q - k + 1)) / ∏ k ∈ Icc 1 q, L (e + k)

def HermitianSumValuationBound : Prop :=
  ∀ (K : Type) [Field K] (v vc : AddValuation K (WithTop ℝ)) (conj : K →+* K),
    (∀ x, v (conj x) = vc x) →
    ∀ (ι κ : Type) [Fintype κ] (X : Finset ι) (z z' : ι → κ → K) (gm : ι → κ → κ → K)
      (c0 : K) (δ : ℝ), c0 ≠ 0 →
    (∀ x ∈ X, ∀ k, z x k = c0 * z' x k) →
    (∀ x ∈ X, ∀ k, ((-δ : ℝ) : WithTop ℝ) ≤ v (z x k) ∧ ((-δ : ℝ) : WithTop ℝ) ≤ vc (z x k) ∧
      ((-δ : ℝ) : WithTop ℝ) ≤ v (z' x k) ∧ ((-δ : ℝ) : WithTop ℝ) ≤ vc (z' x k)) →
    (∀ x ∈ X, ∀ k l, ((-δ : ℝ) : WithTop ℝ) ≤ v (gm x k l)) →
    v c0 ≤ v (∑ x ∈ X, ∑ k, ∑ l, z x k * conj (z x l) * gm x k l) + ((3 * δ : ℝ) : WithTop ℝ) ∧
    v c0⁻¹ ≤ v (∑ x ∈ X, ∑ k, ∑ l, z' x k * conj (z' x l) * gm x k l) + ((3 * δ : ℝ) : WithTop ℝ) ∧
    ((-(3 * δ) : ℝ) : WithTop ℝ) ≤ v (∑ x ∈ X, ∑ k, ∑ l, z x k * conj (z x l) * gm x k l) ∧
    ((-(3 * δ) : ℝ) : WithTop ℝ) ≤ v (∑ x ∈ X, ∑ k, ∑ l, z' x k * conj (z' x l) * gm x k l)

def GaussSumTwist : Prop :=
  ∀ (R : Type) [CommRing R] [Fintype R] [DecidableEq R] (I : Ideal R) (ψ : AddChar R ℂ)
    (ν dl : Rˣ →* ℂˣ) (c : R) (x0 : Rˣ),
    (∀ y ∈ I, ∀ y' ∈ I, y * y' = 0) →
    (∀ z : R, (∀ y ∈ I, ψ (z * y) = 1) → z ∈ I) →
    (∀ u : Rˣ, (u : R) - 1 ∈ I → ((ν u : ℂˣ) : ℂ) = ψ (c * ((u : R) - 1))) →
    (∀ u : Rˣ, (u : R) - 1 ∈ I → dl u = 1) →
    (x0 : R) - c ∈ I →
    (∑ x : Rˣ, (((ν x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) =
      (Nat.card I : ℂ) * ((((ν x0)⁻¹ : ℂˣ) : ℂ) * ψ (x0 : R))) ∧
    (∑ x : Rˣ, ((((ν * dl) x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) =
      (((dl x0)⁻¹ : ℂˣ) : ℂ) * ∑ x : Rˣ, (((ν x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R))

def TowerValuationBound : Prop :=
  ∀ (G : Type) [CommGroup G] (v : G → ℝ), (∀ x y, v (x * y) = v x + v y) →
    ∀ (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    ∀ (T Td Tdp ρ E : ℤ → G) (N0 ε δ σ : ℝ), 0 ≤ N0 → 0 ≤ ε →
    (∀ s : ℤ, 1 ≤ s → s ≤ h →
      ρ s = Tdp s / T s ∧ -N0 ≤ v (Tdp s) ∧ v (Tdp s) ≤ v (Td s) + ε) →
    (∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 → ρ s = E s * ρ (1 - s) ∧ v (E s) = 0) →
    ∀ (c0 c00 A A0 A0' : G), v c0 ≤ v A + 3 * δ → -v c00 ≤ v A0' + 3 * δ →
    A / A0 = ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), ρ s →
    ∀ (ub ua : ℕ → G), (∀ j, j < q → v (ub j) ≤ σ) → (∀ i, i < p → v (ua i) ≤ σ) →
    ∀ r : G, r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) *
        (∏ k ∈ Icc 1 p, ρ ((e : ℤ) + q - k + 1)) * (∏ k ∈ Icc 1 q, ρ ((e : ℤ) + k))⁻¹ →
    v r ≤ |v A0| + |v A0'| + 4 * (∑ s ∈ Icc (1 : ℤ) h, (|v (T s)| + |v (Td s)|)) +
      d * (N0 + ε) + 6 * δ + (p + q : ℕ) * σ

def PrimeLogSquareSumLtOne : Prop :=
  ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 < 1

def PrimeLogBudget : Prop :=
  ∀ (N0 : ℕ → ℝ) (BN0 : ℝ),
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 l * Real.log l ≤ BN0) →
    ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN0 + 1

def GridValuationBound : Prop :=
  ∀ (W X S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ) (N0 : ℕ → ℝ)
    (vr : W → Fin m × Fin m → ℝ) (vx : W → X → ℝ) (XX : Fin m × Fin m → Bool → Finset X)
    (ch : W → Bool) (dd yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (H : X → ℝ) (B BN Bδ : ℝ) (W0 : Finset W),
    (∀ w, 0 ≤ lam w) → (∀ w, 0 ≤ δ w) → (∀ l, 0 ≤ N0 l) → (∀ w s, 0 ≤ vq w s) →
    (∀ w, (ell w).Prime) →
    (∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l) →
    (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) → (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ W0, ∀ ij, vr w ij ≤ (∑ x ∈ XX ij (ch w), |vx w x|) +
      dd ij * (N0 (ell w) + ((ell w : ℝ) ^ 2)⁻¹) + 6 * δ w +
      2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) →
    (∀ (x : X) (F : Finset W), ∑ w ∈ F, lam w * |vx w x| ≤ H x) →
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN) →
    (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
    (∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) →
    (∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) +
      (m : ℝ) ^ 2 * (2 * N * BN + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))) ∧
    (0 ≤ B → (∀ x, H x ≤ B) → (∀ ij b, (XX ij b).card ≤ 2 + 8 * N) →
      ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
        (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ +
          4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) ∧
      ∑ w ∈ W0, lam w * ((∑ ij, vr w ij) + δ w) ≤
        (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ +
          4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) + Bδ)

def GridValuationBoundSquares : Prop :=
  ∀ (W S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ) (N0 : ℕ → ℝ)
    (vr vA vA' : W → Fin m × Fin m → ℝ) (vT : W → Fin m × Fin m → ℤ → ℝ)
    (vTd : W → Fin m × Fin m → Bool → ℤ → ℝ)
    (ch : W → Bool) (dd hh yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (B BN Bδ : ℝ) (W0 : Finset W),
    (∀ w, 0 ≤ lam w) → (∀ w, 0 ≤ δ w) → (∀ l, 0 ≤ N0 l) → (∀ w s, 0 ≤ vq w s) →
    (∀ w, (ell w).Prime) →
    (∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ W0, ∀ ij, vr w ij ≤ |vA w ij| + |vA' w ij| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij (ch w) s|)) +
      dd ij * (N0 (ell w) + ((ell w : ℝ) ^ 2)⁻¹) + 6 * δ w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * vq w s)) →
    (∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA w ij| ≤ B) →
    (∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA' w ij| ≤ B) →
    (∀ ij s (F : Finset W), ∑ w ∈ F, lam w * |vT w ij s| ≤ B) →
    (∀ ij b s (F : Finset W), ∑ w ∈ F, lam w * |vTd w ij b s| ≤ B) →
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN) →
    (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
    (∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) →
    ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ +
        4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))

end Formalism.ValuationGridEstimates
end
end

-- bundled from Formalism.TowerValuationBounds.TowerValuationBoundIndexed
section
noncomputable section

namespace Formalism.ValuationGridEstimates

open Finset

def TowerValuationBoundIndexed : Prop :=
  ∀ (G : Type) [CommGroup G] (v : G → ℝ), (∀ x y, v (x * y) = v x + v y) →
    ∀ (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    ∀ (T Td Tdp ρ E : ℤ → G) (N0 : ℤ → ℝ) (ε δ σ : ℝ),
    (∀ s : ℤ, 1 ≤ s → s ≤ h →
      0 ≤ N0 s ∧ ρ s = Tdp s / T s ∧ -N0 s ≤ v (Tdp s) ∧ v (Tdp s) ≤ v (Td s) + ε) →
    (∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 → ρ s = E s * ρ (1 - s) ∧ v (E s) = 0) →
    ∀ (c0 c00 A A0 A0' : G), v c0 ≤ v A + 3 * δ → -v c00 ≤ v A0' + 3 * δ →
    A / A0 = ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), ρ s →
    ∀ (ub ua : ℕ → G), (∀ j, j < q → v (ub j) ≤ σ) → (∀ i, i < p → v (ua i) ≤ σ) →
    ∀ r : G, r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) *
        (∏ k ∈ Icc 1 p, ρ ((e : ℤ) + q - k + 1)) * (∏ k ∈ Icc 1 q, ρ ((e : ℤ) + k))⁻¹ →
    v r ≤ v A0 + v A0' + 3 * (∑ s ∈ Icc (1 : ℤ) h, |v (T s)|) + 2 * (∑ s ∈ Icc (1 : ℤ) h, |v (Td s)|) +
      ((a : ℝ) - p) * ε + 5 * (∑ s ∈ Icc (1 : ℤ) h, N0 s) + 6 * δ + (p + q : ℕ) * σ

def GridValuationBoundIndexed : Prop :=
  ∀ (W X S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
    (vr : W → Fin m × Fin m → ℝ) (vx : W → X → ℝ) (XX : Fin m × Fin m → Bool → Finset X)
    (ch : W → Bool) (dd hh yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (H : X → ℝ) (BN Bδ : ℝ) (W0 : Finset W),
    (∀ w, 0 ≤ lam w) → (∀ w, 0 ≤ δ w) → (∀ ij s l, 0 ≤ N0 ij s l) → (∀ w s, 0 ≤ vq w s) →
    (∀ w, (ell w).Prime) →
    (∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ W0, ∀ ij, vr w ij ≤ (∑ x ∈ XX ij (ch w), |vx w x|) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ + 6 * δ w +
      2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) →
    (∀ (x : X) (F : Finset W), ∑ w ∈ F, lam w * |vx w x| ≤ H x) →
    (∀ ij (s : ℤ) (P : Finset ℕ), (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 ij s l * Real.log l ≤ BN) →
    (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
    (∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) →
    ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) +
      (m : ℝ) ^ 2 * (10 * N * BN + 2 * N + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))

end Formalism.ValuationGridEstimates
end
end

