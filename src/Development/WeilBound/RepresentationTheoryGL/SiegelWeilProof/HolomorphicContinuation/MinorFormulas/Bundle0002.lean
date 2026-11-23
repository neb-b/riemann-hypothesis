module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorCore

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def SPrime : Prop :=
  ∀ (n m : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → m < n → ∀ (t : ℝ), t ≠ 0 → ∀ β : E n, (herm β).det ≠ 0 →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
      (∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re → Integrable (fun y => cls s z m 0 1 y * chr t β y) ∧
        W z = ∫ y, cls s z m 0 1 y * chr t β y) ∧
      ∀ j < n - m, iteratedDeriv j W 0 = 0

abbrev Fm (n : ℕ) := MvPolynomial (Bool × Fin n × Fin n) (Polynomial ℂ)

def yv (b : Bool) (i j : Fin n) : Fm n := MvPolynomial.X (b, i, j)

def opH (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  let c : ℂ := if b then Complex.I * s else -(Complex.I * s)
  let α : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X
  (-(c : ℂ)) • (LinearMap.mulLeft ℂ (MvPolynomial.C α * yv b l k)).restrictScalars ℂ +
    ∑ a : Fin n, ∑ d : Fin n, (-(c : ℂ)) •
      (LinearMap.mulLeft ℂ (yv b a k * yv b l d) ∘ₗ (MvPolynomial.pderiv (b, a, d)).toLinearMap.restrictScalars ℂ)

def opD (s : ℂ) (m : ℕ) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n := opH s m false k l + opH s m true k l

def cayF (s : ℂ) (m : ℕ) : Fm n →ₗ[ℂ] Fm n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => opD s m k (σ k) ∘ₗ g) LinearMap.id

def DivZ (i : ℕ) (Q : Fm n) : Prop := ∀ e, Polynomial.X ^ i ∣ AddMonoidAlgebra.coeff Q e

def Comm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n),
    opH s m b k l ∘ₗ opH s m b' k' l' = opH s m b' k' l' ∘ₗ opH s m b k l

def Bridge : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m N : ℕ) (z : ℂ) (B : MC n), B ∈ OmS s →
    (cay^[N] (clsC s z m 0 1)) B = clsC s z m 0 1 B *
      MvPolynomial.eval (fun k : Bool × Fin n × Fin n => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
        else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) (MvPolynomial.map (Polynomial.evalRingHom z) ((cayF s m)^[N] 1))

def minorOp (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : Fm n →ₗ[ℂ] Fm n :=
  ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange ρ).foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id

def MinorZ : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m i N : ℕ), i ≤ N → ∀ (I J : Fin (m + i) ↪ Fin n),
    DivZ i ((minorOp s m false I J)^[N] 1)

def MinorZ' : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m j N : ℕ), j ≤ N → ∀ (I J : Fin j ↪ Fin n),
    DivZ j ((minorOp s m true I J)^[N] 1)

abbrev PAB (n : ℕ) := MvPolynomial (Bool × Fin n × Fin n) ℂ

def minorPolynomial (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : PAB n :=
  Matrix.det (fun p q : Fin ρ => (MvPolynomial.X (b, I p, J q) : PAB n))

def Null : Prop :=
  ∀ (n m : ℕ), m < n → ∀ N₀ : ℕ, ∃ N : ℕ,
    (Matrix.det (fun p q : Fin n => (MvPolynomial.X (false, p, q) + MvPolynomial.X (true, p, q) : PAB n))) ^ N ∈
      Ideal.span {x : PAB n | ∃ i j : ℕ, i + j = n - m ∧
        ((i = 0 ∧ j = 0 ∧ x = 1) ∨
         (i = 0 ∧ 0 < j ∧ ∃ (I J : Fin j ↪ Fin n), x = minorPolynomial true I J ^ N₀) ∨
         (0 < i ∧ j = 0 ∧ ∃ (I J : Fin (m + i) ↪ Fin n), x = minorPolynomial false I J ^ N₀) ∨
         (0 < i ∧ 0 < j ∧ ∃ (I J : Fin (m + i) ↪ Fin n) (I' J' : Fin j ↪ Fin n),
            x = minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀))}

def CayDiv : Prop :=
  ∀ (n m : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → m < n → ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → DivZ (n - m) ((cayF s m)^[N] (1 : Fm n))

def MinorFormula : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m : ℕ) (b : Bool) (ρ N : ℕ) (I J : Fin ρ ↪ Fin n),
    (minorOp s m b I J)^[N] 1 =
      MvPolynomial.C (Polynomial.C (((if b then Complex.I * s else -(Complex.I * s)) ^ ρ) ^ N) *
        ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ,
          (-(if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X) - Polynomial.C ((l : ℂ) - i))) *
      (Matrix.det (fun p q : Fin ρ => yv b (J p) (I q))) ^ N

def CayDivOf : Prop := Comm → MinorZ → MinorZ' → Null → CayDiv

def SPrimeOf : Prop := Bridge → CayDiv → SPrime

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorIter
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R] {ρ : ℕ}

theorem del_C_mul (p q : Fin ρ) (r : R) (g : Pm R ρ) : del p q (C r * g) = C r * del p q g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero]

theorem opE_C_mul' (α : R) (p q : Fin ρ) (r : R) (g : Pm R ρ) : opE α p q (C r * g) = C r * opE α p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, del_C_mul]
  ring

theorem del_det_pow (p q : Fin ρ) (k : ℕ) :
    del p q ((Xm R ρ).det ^ k) = (k : Pm R ρ) * X (q, p) * (Xm R ρ).det ^ k := by
  rw [Derivation.leibniz_pow, delDet, smul_eq_mul, nsmul_eq_mul]
  rcases k with _ | k
  · simp
  · rw [pow_succ]
    push_cast
    ring

theorem opE_det_pow_mul (α : R) (p q : Fin ρ) (k : ℕ) (g : Pm R ρ) :
    opE α p q ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * opE (α + k) p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, del_det_pow]
  simp only [map_add (f := _), map_natCast]
  ring

theorem foldr_det_pow (α : R) (k : ℕ) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) ((Xm R ρ).det ^ k * g) =
      (Xm R ρ).det ^ k * (L.foldr (fun j h => opE (α + k) j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_det_pow_mul]

theorem detE_det_pow_mul (α : R) (k : ℕ) (g : Pm R ρ) :
    detE α ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * detE (α + k) g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_det_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

theorem foldr_C_mul (α : R) (r : R) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) (C r * g) =
      C r * (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_C_mul']

theorem detE_C_mul (α : R) (r : R) (g : Pm R ρ) : detE α (C r * g) = C r * detE α g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

theorem iter : Iter := by
  intro R _ ρ α N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    have hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (C α + (l : Pm R ρ) - (i : Pm R ρ))) =
        C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))) := by
      simp [map_prod]
    set r := ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))
    have h1 : (C r : Pm R ρ) = C r * 1 := (mul_one _).symm
    rw [hc, mul_comm, detE_det_pow_mul, h1, detE_C_mul, core]
    rw [Finset.prod_range_succ, hc]
    simp only [map_prod, map_sub, map_add (f := _), map_natCast]
    ring

end PositivityTheory.Rg.Sw.SP.Mi
end
end

