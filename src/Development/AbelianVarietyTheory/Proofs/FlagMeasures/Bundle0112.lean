module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormExpSubOneLeExpNorm
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

namespace NearUnitaryExp

open scoped Matrix.Norms.Frobenius

theorem norm_exp_sub_one_le_exp_norm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (x : A) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hx := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have hr := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at hr
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at hx hr
  refine hx.norm_le_of_bounded hr fun m => ?_
  rw [norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos m)) (by positivity)

variable {n : ℕ}

theorem sqrt_hs_eq_norm (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow, hs]
  simp only [Real.rpow_two]

theorem hs_nonneg' (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_eq_hs (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = hs A := by
  rw [← sqrt_hs_eq_norm, Real.sq_sqrt (hs_nonneg' A)]

private lemma re_star_mul_self_eq_norm_sq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem hs_eq_re_trace (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    re_star_mul_self_eq_norm_sq]
  exact Finset.sum_comm

theorem norm_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ‖k * A‖ = ‖A‖ := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  rw [← sqrt_hs_eq_norm, ← sqrt_hs_eq_norm, hs_eq_re_trace, hs_eq_re_trace, conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k A, hk', Matrix.one_mul]

theorem norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [← sqrt_hs_eq_norm, hs_eq_re_trace]
  simp

theorem norm_trace_le (A : Matrix (Fin n) (Fin n) ℂ) : ‖A.trace‖ ≤ Real.sqrt n * ‖A‖ := by
  have hdiag : ∑ i, ‖A i i‖ ^ 2 ≤ hs A :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (∑ i, ‖A i i‖) ^ 2 ≤ (Real.sqrt n * ‖A‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), norm_sq_eq_hs]
    calc (∑ i, ‖A i i‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, ‖A i i‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ n * hs A := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)
  have h1 : ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
  have h2 : 0 ≤ ∑ i, ‖A i i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h3 : 0 ≤ Real.sqrt n * ‖A‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

theorem hs_unitary_sub_one {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : hs (k - 1) = 2 * n - 2 * k.trace.re := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hprod : (k - 1)ᴴ * (k - 1) = 1 + 1 - kᴴ - k := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hk',
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hs_eq_re_trace, hprod, trace_sub, trace_sub, trace_add, trace_one, trace_conjTranspose,
    Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re,
    Fintype.card_fin, Complex.natCast_re]
  ring

theorem norm_pow_le_of_unitary {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (E : Matrix (Fin n) (Fin n) ℂ) {c : ℝ}
    (hE : ‖E - 1‖ ≤ c - 1) (j : ℕ) : ‖(k * E) ^ j‖ ≤ c ^ j * Real.sqrt n := by
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul, norm_one_eq]
  | succ j ih =>
    have hsplit : E * (k * E) ^ j = (k * E) ^ j + (E - 1) * (k * E) ^ j := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [pow_succ', Matrix.mul_assoc, norm_unitary_mul hk, hsplit]
    have hm := frobenius_norm_mul (E - 1) ((k * E) ^ j)
    have hn0 := norm_nonneg ((k * E) ^ j)
    have hE0 := norm_nonneg (E - 1)
    calc ‖(k * E) ^ j + (E - 1) * (k * E) ^ j‖
        ≤ ‖(k * E) ^ j‖ + ‖(E - 1) * (k * E) ^ j‖ := norm_add_le _ _
      _ ≤ (1 + ‖E - 1‖) * ‖(k * E) ^ j‖ := by linarith
      _ ≤ c * (c ^ j * Real.sqrt n) := by
          apply mul_le_mul (by linarith) ih hn0 (by linarith)
      _ = c ^ (j + 1) * Real.sqrt n := by ring

theorem near_arch : ∀ (n : ℕ) (k X : Matrix (Fin n) (Fin n) ℂ) (ep : ℝ), k ∈ Matrix.unitaryGroup (Fin n) ℂ → X.IsHermitian → 0 ≤ ep → Real.sqrt (hs X) ≤ ep → n * ep ≤ 1 / 4 → (∀ j : ℕ, j ≤ n → ‖((k * NormedSpace.exp X) ^ j).trace - n‖ ≤ 3 * n) ∧ ((k * NormedSpace.exp X).trace = n → Real.sqrt (hs (k * NormedSpace.exp X - 1)) ≤ 3 * Real.sqrt (n * ep)) := by
  intro n k X ep hk _ hep hXe hne
  have hXn : ‖X‖ ≤ ep := by rwa [sqrt_hs_eq_norm] at hXe
  have hE1 : ‖NormedSpace.exp X - 1‖ ≤ Real.exp ep - 1 := by
    have h1 := norm_exp_sub_one_le_exp_norm X
    have h2 := Real.exp_le_exp.mpr hXn
    exact le_trans h1 (by linarith)
  generalize NormedSpace.exp X = E at hE1 ⊢
  have hpow := norm_pow_le_of_unitary hk E hE1
  have hq : Real.exp (1 / 4) ≤ 3 / 2 := by
    have h := Real.abs_exp_sub_one_le (x := 1 / 4) (by norm_num [abs_of_pos])
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
    linarith [le_abs_self (Real.exp (1 / 4) - 1)]
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  refine ⟨fun j hj => ?_, fun htr => ?_⟩
  · have hje : (j : ℝ) * ep ≤ 1 / 4 := by
      have : (j : ℝ) ≤ n := by exact_mod_cast hj
      nlinarith
    have hcj : Real.exp ep ^ j ≤ 3 / 2 := by
      rw [← Real.exp_nat_mul]
      exact (Real.exp_le_exp.mpr hje).trans hq
    have htr := norm_trace_le ((k * E) ^ j)
    have hb := hpow j
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hbound : ‖((k * E) ^ j).trace‖ ≤ n * (3 / 2) := by
      calc ‖((k * E) ^ j).trace‖ ≤ Real.sqrt n * ‖(k * E) ^ j‖ := htr
        _ ≤ Real.sqrt n * (Real.exp ep ^ j * Real.sqrt n) := mul_le_mul_of_nonneg_left hb hs0
        _ = (Real.sqrt n * Real.sqrt n) * Real.exp ep ^ j := by ring
        _ = n * Real.exp ep ^ j := by rw [hsn]
        _ ≤ n * (3 / 2) := mul_le_mul_of_nonneg_left hcj (Nat.cast_nonneg n)
    calc ‖((k * E) ^ j).trace - n‖ ≤ ‖((k * E) ^ j).trace‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * n := by rw [Complex.norm_natCast]; linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hs]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    set s := Real.sqrt n with hs_def
    set t := Real.sqrt ep with ht_def
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t * t = ep := Real.mul_self_sqrt hep
    have hst : s * t ≤ 1 / 2 := by
      have : (s * t) * (s * t) ≤ 1 / 4 := by
        calc (s * t) * (s * t) = (s * s) * (t * t) := by ring
          _ = n * ep := by rw [hsn, htt]
          _ ≤ 1 / 4 := hne
      nlinarith
    have hep1 : ep ≤ 1 := by nlinarith
    have hdel : ‖E - 1‖ ≤ 2 * ep := by
      have h := Real.abs_exp_sub_one_le (x := ep) (by rw [abs_of_nonneg hep]; exact hep1)
      rw [abs_of_nonneg hep] at h
      linarith [le_abs_self (Real.exp ep - 1)]
    have hsplit : k * E = k + k * (E - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    have htrk : k.trace = n - (k * (E - 1)).trace := by
      rw [← htr, hsplit, trace_add]
      ring
    have hre : (n : ℝ) - s * ‖E - 1‖ ≤ k.trace.re := by
      have h1 := norm_trace_le (k * (E - 1))
      rw [norm_unitary_mul hk, ← hs_def] at h1
      have h2 := Complex.abs_re_le_norm (k * (E - 1)).trace
      rw [htrk, Complex.sub_re, Complex.natCast_re]
      linarith [le_abs_self (k * (E - 1)).trace.re]
    have hk1 : ‖k - 1‖ ^ 2 ≤ 4 * (s * t) ^ 2 := by
      rw [norm_sq_eq_hs, hs_unitary_sub_one hk]
      have hE0 := norm_nonneg (E - 1)
      have : s * ‖E - 1‖ ≤ s * (2 * (t * t)) := by
        rw [htt]; exact mul_le_mul_of_nonneg_left hdel (by linarith)
      nlinarith
    have hk1' : ‖k - 1‖ ≤ 2 * (s * t) := by
      have := norm_nonneg (k - 1)
      have hst0 : 0 ≤ s * t := mul_nonneg (by linarith) ht0
      nlinarith
    have hsum : k * E - 1 = (k - 1) + k * (E - 1) := by
      rw [hsplit]
      abel
    rw [sqrt_hs_eq_norm, Real.sqrt_mul (Nat.cast_nonneg n), hsum]
    calc ‖(k - 1) + k * (E - 1)‖ ≤ ‖k - 1‖ + ‖k * (E - 1)‖ := norm_add_le _ _
      _ ≤ 2 * (s * t) + 2 * (t * t) := by rw [norm_unitary_mul hk, htt]; linarith
      _ ≤ 3 * (s * t) := by nlinarith

end NearUnitaryExp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrderedProductExpExpandingRealSmul
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.ExpChartExpanding

section General
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem norm_exp_sub_one_le (x : A) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1 h2
  refine HasSum.norm_le_of_bounded h1 h2 (fun k => ?_)
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos k)) (by positivity)

theorem norm_exp_smul_sub_one_le {E : A} (hE : ‖E‖ ≤ 1) {s t : ℝ} (ht : t ∈ Set.Icc 0 s) :
    ‖NormedSpace.exp (t • E) - 1‖ ≤ Real.exp s - 1 := by
  refine (norm_exp_sub_one_le _).trans ?_
  have : ‖t • E‖ ≤ s := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, norm_nonneg E]
  linarith [Real.exp_le_exp.2 this]

theorem norm_exp_smul_sub_le {E : A} (hE : ‖E‖ ≤ 1) {s t t' : ℝ} (ht : t ∈ Set.Icc 0 s)
    (ht' : t' ∈ Set.Icc 0 s) :
    ‖NormedSpace.exp (t • E) - NormedSpace.exp (t' • E) - (t - t') • E‖ ≤
      |t - t'| * (Real.exp s - 1) := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun u : ℝ => NormedSpace.exp (u • E) - u • E)
    (f' := fun u : ℝ => NormedSpace.exp (u • E) * E - E) (s := Set.Icc 0 s)
    (C := Real.exp s - 1) (x := t') (y := t)
    (fun u _ => by
      have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) E u).sub ((hasDerivAt_id u).smul_const E)
      rw [one_smul] at h
      exact h.hasDerivWithinAt)
    (fun u hu => by
      have h := norm_exp_smul_sub_one_le hE hu
      have e : NormedSpace.exp (u • E) * E - E = (NormedSpace.exp (u • E) - 1) * E := by
        noncomm_ring
      rw [e]
      refine (norm_mul_le _ _).trans ?_
      nlinarith [norm_nonneg E, norm_nonneg (NormedSpace.exp (u • E) - 1)])
    (convex_Icc 0 s) ht' ht
  have e : NormedSpace.exp (t • E) - NormedSpace.exp (t' • E) - (t - t') • E =
      (NormedSpace.exp (t • E) - t • E) - (NormedSpace.exp (t' • E) - t' • E) := by
    rw [sub_smul]; abel
  rw [e, mul_comm]
  simpa [Real.norm_eq_abs] using key

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem norm_mul_le_left {x y : A} {a : ℝ} (hx : ‖x - 1‖ ≤ a - 1) : ‖x * y‖ ≤ a * ‖y‖ := by
  have e : x * y = (x - 1) * y + y := by noncomm_ring
  rw [e]
  have := norm_add_le ((x - 1) * y) y
  have := norm_mul_le (x - 1) y
  nlinarith [norm_nonneg y]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem norm_mul_le_right {x y : A} {a : ℝ} (hx : ‖x - 1‖ ≤ a - 1) : ‖y * x‖ ≤ ‖y‖ * a := by
  have e : y * x = y * (x - 1) + y := by noncomm_ring
  rw [e]
  have := norm_add_le (y * (x - 1)) y
  have := norm_mul_le y (x - 1)
  nlinarith [norm_nonneg y]

theorem norm_prod_sub_one_le {s : ℝ} : ∀ (m : ℕ) (E : Fin m → A) (t : Fin m → ℝ),
    (∀ i, ‖E i‖ ≤ 1) → (∀ i, t i ∈ Set.Icc 0 s) →
    ‖(List.ofFn fun i => NormedSpace.exp (t i • E i)).prod - 1‖ ≤ Real.exp (m * s) - 1
  | 0, E, t, _, _ => by simp
  | m + 1, E, t, hE, ht => by
    rw [List.ofFn_succ, List.prod_cons]
    have ih := norm_prod_sub_one_le m (fun i => E i.succ) (fun i => t i.succ)
      (fun i => hE _) (fun i => ht _)
    have h0 := norm_exp_smul_sub_one_le (hE 0) (ht 0)
    set P := (List.ofFn fun i : Fin m => NormedSpace.exp (t i.succ • E i.succ)).prod
    set x := NormedSpace.exp (t 0 • E 0)
    have e : x * P - 1 = x * (P - 1) + (x - 1) := by noncomm_ring
    have h1 := norm_mul_le_left (y := P - 1) h0
    have h2 := norm_add_le (x * (P - 1)) (x - 1)
    have h3 : Real.exp (((m + 1 : ℕ) : ℝ) * s) = Real.exp s * Real.exp (m * s) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e, h3]
    nlinarith [Real.exp_pos s]

theorem norm_sum_smul_le {m : ℕ} (E : Fin m → A) (d : Fin m → ℝ) (hE : ∀ i, ‖E i‖ ≤ 1) :
    ‖∑ i, d i • E i‖ ≤ ∑ i, |d i| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  nlinarith [abs_nonneg (d i), hE i]

theorem norm_prod_sub_prod_sub_le {s : ℝ} : ∀ (m : ℕ) (E : Fin m → A) (t t' : Fin m → ℝ),
    (∀ i, ‖E i‖ ≤ 1) → (∀ i, t i ∈ Set.Icc 0 s) → (∀ i, t' i ∈ Set.Icc 0 s) →
    ‖(List.ofFn fun i => NormedSpace.exp (t i • E i)).prod -
      (List.ofFn fun i => NormedSpace.exp (t' i • E i)).prod - ∑ i, (t i - t' i) • E i‖ ≤
      (∑ i, |t i - t' i|) * (Real.exp (m * s) - 1)
  | 0, E, t, t', _, _, _ => by simp
  | m + 1, E, t, t', hE, ht, ht' => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    have ih := norm_prod_sub_prod_sub_le m (fun i => E i.succ) (fun i => t i.succ)
      (fun i => t' i.succ) (fun i => hE _) (fun i => ht _) (fun i => ht' _)
    have hP := norm_prod_sub_one_le m (fun i => E i.succ) (fun i => t i.succ)
      (fun i => hE _) (fun i => ht _)
    have hS := norm_sum_smul_le (fun i : Fin m => E i.succ) (fun i => t i.succ - t' i.succ)
      (fun i => hE _)
    have h0 := norm_exp_smul_sub_one_le (hE 0) (ht' 0)
    have h1 := norm_exp_smul_sub_le (hE 0) (ht 0) (ht' 0)
    have hD : ‖(t 0 - t' 0) • E 0‖ ≤ |t 0 - t' 0| := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (t 0 - t' 0), hE 0]
    have hL : 0 ≤ ∑ i : Fin m, |t i.succ - t' i.succ| := by positivity
    set P := (List.ofFn fun i : Fin m => NormedSpace.exp (t i.succ • E i.succ)).prod
    set P' := (List.ofFn fun i : Fin m => NormedSpace.exp (t' i.succ • E i.succ)).prod
    set x := NormedSpace.exp (t 0 • E 0)
    set x' := NormedSpace.exp (t' 0 • E 0)
    set S := ∑ i : Fin m, (t i.succ - t' i.succ) • E i.succ
    set L := ∑ i : Fin m, |t i.succ - t' i.succ|
    set D := (t 0 - t' 0) • E 0
    have hd := abs_nonneg (t 0 - t' 0)
    set d := |t 0 - t' 0|
    have e : x * P - x' * P' - (D + S) =
        (x - x' - D) * P + D * (P - 1) + x' * (P - P' - S) + (x' - 1) * S := by noncomm_ring
    have h3 : Real.exp (((m + 1 : ℕ) : ℝ) * s) = Real.exp s * Real.exp (m * s) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e, h3]
    have ha := Real.exp_pos s
    have hb := Real.exp_pos (m * s)
    set a := Real.exp s
    set b := Real.exp (m * s)
    have k1 : ‖(x - x' - D) * P‖ ≤ d * (a - 1) * b :=
      (norm_mul_le_right hP).trans (mul_le_mul_of_nonneg_right h1 hb.le)
    have k2 : ‖D * (P - 1)‖ ≤ d * (b - 1) :=
      (norm_mul_le _ _).trans (mul_le_mul hD hP (norm_nonneg _) hd)
    have k3 : ‖x' * (P - P' - S)‖ ≤ a * (L * (b - 1)) :=
      (norm_mul_le_left h0).trans (mul_le_mul_of_nonneg_left ih ha.le)
    have k4 : ‖(x' - 1) * S‖ ≤ (a - 1) * L :=
      (norm_mul_le _ _).trans (mul_le_mul h0 hS (norm_nonneg _) ((norm_nonneg _).trans h0))
    have k5 := norm_add₄_le (a := (x - x' - D) * P) (b := D * (P - 1)) (c := x' * (P - P' - S))
      (d := (x' - 1) * S)
    nlinarith

end General

theorem hs_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = ((g * gᴴ).trace).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem hs_sum_smul {n m : ℕ} (E : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) (d : Fin m → ℝ) :
    hs (∑ i, d i • E i) = ∑ i, d i ^ 2 := by
  rw [hs_eq_trace, Matrix.conjTranspose_sum, Finset.sum_mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_sum, Complex.re_sum]
  have : ∀ j, ((d i • E i * (d j • E j)ᴴ).trace).re = if i = j then d i * d j else 0 := by
    intro j
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_smul, Complex.smul_re, h]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => this j]
  simp [sq]

section Frob
open scoped Matrix.Norms.Frobenius

theorem sqrt_hs {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs g) = ‖g‖ := by
  rw [Matrix.frobenius_norm_def, hs, Real.sqrt_eq_rpow]
  simp

theorem orderedProductExp_expanding_real_smul (n : ℕ) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (hs0 : 0 ≤ s)
    (h : ∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0)
    (t t' : Fin (n ^ 2) → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 s ∧ t' i ∈ Set.Icc 0 s) :
    Real.sqrt (∑ i, (t i - t' i) ^ 2) * (1 - n * (Real.exp (3 * n ^ 2 * s) - 1)) ≤
      Real.sqrt (hs ((List.ofFn fun i => NormedSpace.exp (t i • E i)).prod -
        (List.ofFn fun i => NormedSpace.exp (t' i • E i)).prod)) := by
  have hE : ∀ i, ‖E i‖ ≤ 1 := fun i => by
    rw [← sqrt_hs, hs_eq_trace, h]; simp
  have key := norm_prod_sub_prod_sub_le (A := Matrix (Fin n) (Fin n) ℂ) (n ^ 2) E t t' hE
    (fun i => (ht i).1) (fun i => (ht i).2)
  have hS : ‖∑ i, (t i - t' i) • E i‖ = Real.sqrt (∑ i, (t i - t' i) ^ 2) := by
    rw [← sqrt_hs, hs_sum_smul E h]
  have hL : ∑ i, |t i - t' i| ≤ n * Real.sqrt (∑ i, (t i - t' i) ^ 2) := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |t i - t' i|)
    simp only [sq_abs, Finset.card_univ, Fintype.card_fin] at h1
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact_mod_cast h1
  have hb : Real.exp (((n ^ 2 : ℕ) : ℝ) * s) - 1 ≤ Real.exp (3 * n ^ 2 * s) - 1 := by
    have : ((n ^ 2 : ℕ) : ℝ) * s ≤ 3 * n ^ 2 * s := by
      push_cast
      have : 0 ≤ (n : ℝ) ^ 2 * s := by positivity
      linarith
    linarith [Real.exp_le_exp.2 this]
  have hb0 : 0 ≤ Real.exp (((n ^ 2 : ℕ) : ℝ) * s) - 1 := by
    have : 0 ≤ ((n ^ 2 : ℕ) : ℝ) * s := by positivity
    linarith [Real.add_one_le_exp (((n ^ 2 : ℕ) : ℝ) * s)]
  have k := key.trans (mul_le_mul hL hb hb0 (by positivity))
  have fin : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, X = Y →
      ‖X - ∑ i, (t i - t' i) • E i‖ ≤
        n * Real.sqrt (∑ i, (t i - t' i) ^ 2) * (Real.exp (3 * n ^ 2 * s) - 1) →
      Real.sqrt (∑ i, (t i - t' i) ^ 2) * (1 - n * (Real.exp (3 * n ^ 2 * s) - 1)) ≤
        Real.sqrt (hs Y) := by
    rintro X _ rfl hX
    rw [sqrt_hs]
    have tri := norm_sub_norm_le (∑ i, (t i - t' i) • E i) X
    rw [norm_sub_rev, hS] at tri
    linarith
  exact fin _ _ rfl k

end Frob

theorem expanding : ∀ (n : ℕ) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s → (∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) → ∀ t t' : Fin (n ^ 2) → ℝ, (∀ i, t i ∈ Set.Icc 0 s ∧ t' i ∈ Set.Icc 0 s) → Real.sqrt (∑ i, (t i - t' i) ^ 2) * (1 - n * (Real.exp (3 * n ^ 2 * s) - 1)) ≤ Real.sqrt (hs ((List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod - (List.ofFn fun i => NormedSpace.exp ((t' i : ℂ) • E i)).prod)) := by
  intro n E s hs0 h t t' ht
  simp only [Complex.coe_smul]
  exact orderedProductExp_expanding_real_smul n E s hs0 h t t' ht

end GlobalTheory.ExpChartExpanding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOnGExistsContDiffCompactSupportExtension
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

theorem smoothOnG_exists_contDiff_compactSupport_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (β : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε β →
      HasCompactSupport (fun g : UJ ε => β (umat g)) →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        ∀ g : UJ ε, β (umat g) = F (fun i j => umat g i j) := by
  intro n ε β hβ hc
  obtain ⟨F₀, hF₀, hF₀eq⟩ := smoothOnG_exists_contDiff_extension n ε β hβ

  have hp : Continuous (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
    have hu : Continuous (fun g : UJ ε => umat g) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_pi fun i => continuous_pi fun j => hu.matrix_elem i j

  have hK : IsCompact ((fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) ''
      tsupport (fun g : UJ ε => β (umat g))) := hc.isCompact.image hp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0

  let χ : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun x => (χ x : ℂ) * F₀ x, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hF₀
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro g
    have h₀ : F₀ (fun i j => umat g i j) = β (umat g) := hF₀eq (umat g) g.2
    by_cases hz : β (umat g) = 0
    · show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [h₀, hz, mul_zero]
    · have hmem : (fun i j => umat g i j : Fin n → Fin n → ℂ) ∈ Metric.closedBall 0 χ.rIn := by
        refine Metric.closedBall_subset_closedBall ?_ (hR ⟨g, subset_tsupport _ hz, rfl⟩)
        show R ≤ max R 0 + 1
        linarith [le_max_left R 0]
      show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [χ.one_of_mem_closedBall hmem, h₀, Complex.ofReal_one, one_mul]

end GlobalTheory
end

