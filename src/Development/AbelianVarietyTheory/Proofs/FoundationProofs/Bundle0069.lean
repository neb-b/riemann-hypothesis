module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDivSqrtLeFourExp
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem badBound_tail (eps C : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in Filter.atTop,
      612 * (x ^ C) ^ 3 * Real.exp (-(x ^ (eps / 6))) ≤ Real.exp (-(x ^ (eps / 7))) := by
  have hb : 0 < eps / 7 := by positivity
  have hab : 0 < eps / 6 - eps / 7 := by linarith
  have h612 : 0 ≤ Real.log 612 := Real.log_nonneg (by norm_num)
  set K : ℝ := 1 + Real.log 612 + 3 * |C| / (eps / 7) with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (K ^ (1 / (eps / 6 - eps / 7)))] with x hx1 hxK
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxb : 1 ≤ x ^ (eps / 7) := Real.one_le_rpow hx1 hb.le
  have hl : Real.log x ≤ x ^ (eps / 7) / (eps / 7) := Real.log_le_rpow_div hx0.le hb
  have hd : K ≤ x ^ (eps / 6 - eps / 7) := by
    calc K = (K ^ (1 / (eps / 6 - eps / 7))) ^ (eps / 6 - eps / 7) := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel hab.ne', Real.rpow_one]
      _ ≤ x ^ (eps / 6 - eps / 7) := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hxK hab.le
  have hsplit : x ^ (eps / 6) = x ^ (eps / 6 - eps / 7) * x ^ (eps / 7) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hpow : (x ^ C) ^ 3 = Real.exp (3 * (Real.log x * C)) := by
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; norm_num
  rw [hpow, show (612 : ℝ) = Real.exp (Real.log 612) from (Real.exp_log (by norm_num)).symm,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hC1 : Real.log x * C ≤ Real.log x * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hlog
  have hC2 : Real.log x * |C| ≤ x ^ (eps / 7) / (eps / 7) * |C| :=
    mul_le_mul_of_nonneg_right hl (abs_nonneg C)
  have hKx : K * x ^ (eps / 7) ≤ x ^ (eps / 6) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hl612 : Real.log 612 ≤ Real.log 612 * x ^ (eps / 7) := le_mul_of_one_le_right h612 hxb
  have h3 : 3 * (Real.log x * C) ≤ 3 * |C| / (eps / 7) * x ^ (eps / 7) := by
    calc 3 * (Real.log x * C) ≤ 3 * (x ^ (eps / 7) / (eps / 7) * |C|) := by linarith
      _ = 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  have h4 : (1 + Real.log 612 + 3 * |C| / (eps / 7)) * x ^ (eps / 7) =
      x ^ (eps / 7) + Real.log 612 * x ^ (eps / 7) + 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  rw [hK, h4] at hKx
  linarith

theorem log_div_sqrt_le_four_exp {g u : ℝ} (hg : Real.exp (4 * u) ≤ g) :
    Real.log g / Real.sqrt g ≤ 4 * Real.exp (-u) := by
  have hg0 : 0 < g := lt_of_lt_of_le (Real.exp_pos _) hg
  set q := g ^ (1 / 4 : ℝ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hg0 _
  have h1 : Real.log g ≤ g ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hg0.le (by norm_num)
  have hs : Real.sqrt g = q * q := by
    rw [hqdef, ← Real.rpow_add hg0, Real.sqrt_eq_rpow]; norm_num
  have hq : Real.exp u ≤ q := by
    have : Real.exp u = (Real.exp (4 * u)) ^ (1 / 4 : ℝ) := by
      rw [← Real.exp_mul]; ring_nf
    rw [this]; exact Real.rpow_le_rpow (Real.exp_pos _).le hg (by norm_num)
  have hone : 1 ≤ Real.exp (-u) * q := by
    calc (1 : ℝ) = Real.exp (-u) * Real.exp u := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp (-u) * q := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
  rw [hs, div_le_iff₀ (by positivity)]
  have h1' : Real.log g ≤ 4 * q := by rw [← hqdef] at h1; linarith
  nlinarith [hq0, hone]

theorem badBound_numbers : ∀ eps C : ℝ, 0 < eps → eps ≤ 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (g f m N q : ℝ), Real.exp (8 * x ^ eps) ≤ g → x ^ (2 : ℝ) ≤ f → f ≤ x ^ C → 0 ≤ m → m ≤ x ^ C → x ^ eps ≤ N → N ≤ x ^ C → Real.exp (x ^ (eps / 6)) ≤ q → 100000 ≤ N ∧ 0 ≤ badBound g f m N q ∧ 6 * badBound g f m N q ≤ Real.exp (-(x ^ (eps / 7))) := by
  intro eps C he he1
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 (badBound_tail eps C he)
  refine ⟨max (max X1 8) (max (20 * |C| + 1) ((100000 : ℝ) ^ (1 / eps))), ?_⟩
  intro x hx g f m N q hg hf1 hf2 hm1 hm2 hN1 hN2 hq
  have hxX1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx8 : 8 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC : 20 * |C| + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxN : (100000 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx1' : 1 < x := by linarith
  have hNbig : 100000 ≤ N := by
    have e : (100000 : ℝ) = ((100000 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]
    have h2 : ((100000 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hxN he.le
    linarith
  have hTail := hX1 x hxX1
  have hCe : eps ≤ C := (Real.rpow_le_rpow_left_iff hx1').1 (le_trans hN1 hN2)
  have hC0 : 0 ≤ C := by linarith
  set P := x ^ C with hP
  set E := Real.exp (-(x ^ (eps / 6))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hN0 : 0 < N := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hx1 hC0
  have hx2 : x ^ (2 : ℝ) = x * x := by rw [Real.rpow_two, sq]
  rw [hx2] at hf1
  have hf0 : 0 ≤ f := le_trans (by positivity) hf1
  have he6 : x ^ (eps / 6) ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have he6h : x ^ (eps / 6) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by rw [← Real.rpow_add hx0]; norm_num
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have hsx : x ^ (1 / 2 : ℝ) ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 he.le
  have hg8 : Real.exp 8 ≤ g := le_trans (Real.exp_le_exp.2 (by linarith)) hg
  have hg2 : 2 ≤ g := by have := Real.add_one_le_exp 8; linarith
  have hg0 : 0 < g := by linarith
  have hEg : 1 ≤ E * g := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * g := mul_le_mul_of_nonneg_left (le_trans (Real.exp_le_exp.2 (by linarith)) hg) hE0.le
  have hginv : 1 / g ≤ E := by rw [div_le_iff₀ hg0]; linarith
  have hT2 : Real.log g / Real.sqrt g ≤ 4 * E := by
    have h := log_div_sqrt_le_four_exp (u := 2 * x ^ eps) (g := g)
      (by rw [show 4 * (2 * x ^ eps) = 8 * x ^ eps by ring]; exact hg)
    refine h.trans ?_
    rw [hE]
    gcongr
    linarith
  have hLg : 0 ≤ Real.log g / Real.sqrt g :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hq0 : 0 < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hEq : 1 ≤ E * q := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * q := mul_le_mul_of_nonneg_left hq hE0.le
  have hqinv : 1 / (4 * q) ≤ E / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlogN : 1 + Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos hN0]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hT3b : (1 + Real.log N) / (g - 1) ≤ 2 * N * E := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := mul_nonneg (mul_nonneg hN0.le hE0.le) (show 0 ≤ g - 2 by linarith)
    have h2 : N * 1 ≤ N * (E * g) := mul_le_mul_of_nonneg_left hEg hN0.le
    linarith
  have hT4 : (7 / 8 : ℝ) ^ f ≤ E := by
    rw [Real.rpow_def_of_pos (by norm_num), hE, Real.exp_le_exp]
    have hl78 : Real.log (7 / 8) ≤ -(1 / 8) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num); linarith
    have h1 : Real.log (7 / 8) * f ≤ -(1 / 8) * f := mul_le_mul_of_nonneg_right hl78 hf0
    have h2 : 8 * x ≤ x * x := mul_le_mul_of_nonneg_right hx8 hx0.le
    linarith
  have hT5 : Real.exp (-(f / (10 * Real.log N))) ≤ E := by
    have hlN0 : 0 < Real.log N := Real.log_pos (by linarith)
    rw [hE, Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
    have hlN : Real.log N ≤ C * Real.log x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log hN0 hN2
    have hlx : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have h1 : x ^ (eps / 6) * (10 * Real.log N) ≤
        x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) := by
      apply mul_le_mul he6h _ (by linarith) hs0
      have : C * Real.log x ≤ C * (x ^ (1 / 2 : ℝ) / (1 / 2)) := mul_le_mul_of_nonneg_left hlx hC0
      linarith
    have h2 : x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) = 20 * C * x := by
      calc x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2))))
          = 20 * C * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
        _ = 20 * C * x := by rw [hsq]
    have h3 : 20 * C * x ≤ x * x := by
      have : 20 * C ≤ x := by have := le_abs_self C; linarith
      exact mul_le_mul_of_nonneg_right this hx0.le
    linarith
  have hgm1 : 0 < g - 1 := by linarith
  unfold badBound
  refine ⟨hNbig, ?_, ?_⟩
  · have t1 : 0 ≤ 3 * f / g := div_nonneg (by linarith) hg0.le
    have t2 : 0 ≤ 23 * f * Real.log g / Real.sqrt g :=
      div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (Real.sqrt_nonneg _)
    have t3 : 0 ≤ 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) hm1)
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
    have t4 : 0 ≤ N / 2 * (7 / 8 : ℝ) ^ f := mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    have t5 : 0 ≤ Real.exp (-(f / (10 * Real.log N))) := (Real.exp_pos _).le
    linarith
  · have b1 : 3 * f / g ≤ 3 * P * E := by
      calc 3 * f / g = 3 * f * (1 / g) := by ring
        _ ≤ 3 * P * E := mul_le_mul (by linarith) hginv (div_nonneg zero_le_one hg0.le) (by linarith)
    have b2 : 23 * f * Real.log g / Real.sqrt g ≤ 92 * P * E := by
      calc 23 * f * Real.log g / Real.sqrt g = 23 * f * (Real.log g / Real.sqrt g) := by ring
        _ ≤ 23 * P * (4 * E) := mul_le_mul (by linarith) hT2 hLg (by linarith)
        _ = 92 * P * E := by ring
    have b3 : 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) ≤ 2 * P * P * (E / 4 + 2 * P * E) := by
      have hfm : 2 * f * m ≤ 2 * P * P := mul_le_mul (by linarith) hm2 hm1 (by linarith)
      have hsum : 1 / (4 * q) + (1 + Real.log N) / (g - 1) ≤ E / 4 + 2 * P * E := by
        have : 2 * N * E ≤ 2 * P * E := mul_le_mul_of_nonneg_right (by linarith) hE0.le
        linarith
      exact mul_le_mul hfm hsum
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    have b4 : N / 2 * (7 / 8 : ℝ) ^ f ≤ P / 2 * E :=
      mul_le_mul (by linarith) hT4 (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have hP0 : 0 ≤ P := by linarith
    have hPP : P ≤ P * P := le_mul_of_one_le_right hP0 hP1
    have hPPP : P * P ≤ P ^ 3 := by
      rw [show P ^ 3 = P * P * P by ring]
      exact le_mul_of_one_le_right (mul_nonneg hP0 hP0) hP1
    have c1 : P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right (hPP.trans hPPP) hE0.le
    have c2 : P * P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right hPPP hE0.le
    have c3 : E ≤ P ^ 3 * E := le_mul_of_one_le_left hE0.le (hP1.trans (hPP.trans hPPP))
    have hnn : 0 ≤ P ^ 3 * E := mul_nonneg (pow_nonneg hP0 3) hE0.le
    linarith

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongrOfBasis
section
noncomputable section

open PowerSeries

namespace GlobalTheory.Col

theorem trace_basis_pow {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (i : Fin p) :
    Algebra.trace B A (b i) = if (i : ℕ) = 0 then (p : B) else 0 := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have hd : ∀ j : Fin p, Algebra.leftMulMatrix b (b i) j j = if (i : ℕ) = 0 then 1 else 0 := by
    intro j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb i, hb j, ← pow_add]
    by_cases h : (i : ℕ) + j < p
    · rw [← hb ⟨_, h⟩, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi, if_pos (Fin.ext (by simp only [Fin.val_mk]; omega))]
      · rw [if_neg hi, if_neg (fun h' => hi (by have := congrArg Fin.val h'; simp only [Fin.val_mk] at this; omega))]
    · have e : x ^ ((i : ℕ) + j) = y • b ⟨(i : ℕ) + j - p, by omega⟩ := by
        rw [hb, Algebra.smul_def, ← hx, ← pow_add]
        congr 1
        simp only [Fin.val_mk]
        omega
      rw [e, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero, if_neg]
      · omega
      · simp only [Fin.ext_iff]
        omega
  simp only [Matrix.diag, hd]
  split_ifs <;> simp

theorem trace_eq_p_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) :
    Algebra.trace B A s = (p : B) * b.repr s ⟨0, hp⟩ := by
  conv_lhs => rw [← b.sum_repr s]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, trace_basis_pow p b x y hb hx, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨0, hp⟩]
  · simp [mul_comm]
  · intro j _ hj
    rw [if_neg, mul_zero]
    intro h0
    exact hj (Fin.ext h0)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem norm_one_add_pow_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : B, Algebra.norm B (1 + (p : A) ^ k * s) = 1 + (p : B) ^ (k + 1) * t := by
  have e : (p : A) ^ k * s = ((p : B) ^ k) • s := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, Algebra.norm_eq_matrix_det b, map_add (f := _), map_one, map_smul, Matrix.det_one_add_smul,
    ← Algebra.trace_eq_matrix_trace b, trace_eq_p_mul p hp b x y hb hx]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨b.repr s ⟨0, hp⟩ + (Matrix.det (1 + (Polynomial.X : Polynomial B) •
    (Algebra.leftMulMatrix b s).map Polynomial.C)).divX.divX.eval (((p : B)) ^ (m + 1)) * (p : B) ^ m, ?_⟩
  ring

theorem normOp_congr_of_basis (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule))
    (hb : ∀ i, b i = (1 + X : PowerSeries R) ^ (i : ℕ))
    (h₁ h₂ r : PowerSeries R) (k : ℕ) (hk : 1 ≤ k) (hu : IsUnit h₂)
    (he : h₁ = h₂ + (p : PowerSeries R) ^ k * r) :
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  letI inst : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  have hx : (1 + X : PowerSeries R) ^ p = algebraMap (PowerSeries R) (PowerSeries R) (1 + X) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (phi_one_add_X (R := R) p hp.out.pos).symm
  have hN : ∀ z, normOp p z = Algebra.norm (PowerSeries R) z := fun z => rfl
  obtain ⟨u, rfl⟩ := hu
  have h1 : h₁ = (u : PowerSeries R) * (1 + (p : PowerSeries R) ^ k * ((↑u⁻¹ : PowerSeries R) * r)) := by
    have hui := u.mul_inv
    linear_combination he - ((p : PowerSeries R) ^ k * r) * hui
  obtain ⟨t, ht⟩ := @norm_one_add_pow_mul (PowerSeries R) (PowerSeries R) _ _ inst p hp.out.pos b (1 + X) (1 + X)
    hb hx ((↑u⁻¹ : PowerSeries R) * r) k hk
  refine ⟨normOp p (u : PowerSeries R) * t, ?_⟩
  rw [h1, hN, hN, map_mul, ht]
  ring

end GlobalTheory.Col
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModP
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem qO_pow_eq (p : ℕ) [Fact p.Prime] (j : ℕ) :
    qO p ^ j = algebraMap (Lau p) (O0 p) (HahnSeries.single (j : ℤ) (1 : ℤ_[p])) := by
  rw [qO, ← map_pow, HahnSeries.single_pow]
  simp

theorem exists_lau_add_p_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (f : Lau p) (z : O0 p), x = algebraMap (Lau p) (O0 p) f + (p : O0 p) * z := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (pI p) x)
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈
      RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [RingHom.mem_ker]
    show AdicCompletion.evalOneₐ (pI p) (x - algebraMap (Lau p) (O0 p) a) = 0
    rw [map_sub, (AdicCompletion.evalOneₐ (pI p)).commutes a]
    show _ - Ideal.Quotient.mk (pI p) a = 0
    rw [ha, sub_self]
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hker, hmap, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨a, z, by rw [← hz]; ring⟩

theorem exists_eq_sum_qO_pow_mul_pow_add_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  obtain ⟨f, z, rfl⟩ := exists_lau_add_p_mul p x
  obtain ⟨g, h, hf⟩ := GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination p f
  refine ⟨fun j => algebraMap (Lau p) (O0 p) (g j), algebraMap (Lau p) (O0 p) h + z, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_add (f := _), map_sum, map_mul, map_natCast]
  simp only [map_mul, map_pow, qO_pow_eq]
  ring

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulApproxPowOfAlmostEtaleSeparatingFamily
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cpow_mul_approx_pow_of_isSep :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  intro L _ v p hp G _ _ hv N _ θ hθ hroot n a b c hs x hx hx1
  have frob := GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime L v p hp
  have trfix := _root_.GlobalTheory.AlmostEt.cosetTrace_fixed_props L v G hv N
  have memN : ∀ y : L, y ∈ Fix L N ↔ ∀ g ∈ N, g • y = y := by
    intro y
    constructor
    · intro h g hg; exact h ⟨g, hg⟩
    · intro h g; exact h g g.2
  have memTop : ∀ y : L, y ∈ Fix L (⊤ : Subgroup G) ↔ ∀ g : G, g • y = y := by
    intro y
    constructor
    · intro h g; exact h ⟨g, Subgroup.mem_top g⟩
    · intro h g; exact h g
  set q₀ : G ⧸ N := ((1 : G) : G ⧸ N) with hq₀
  have hout : ∀ q : G ⧸ N, q.out ∈ N ↔ q = q₀ := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [hq₀, QuotientGroup.eq, mul_one, inv_mem_iff]
  set T : Fin n → L := fun i => cosetTrace N (b i ^ p * x) with hTdef
  have hbx : ∀ i, b i ^ p * x ∈ Fix L N := fun i =>
    Subfield.mul_mem _ (Subfield.pow_mem _ (hs.b_mem i) p) hx
  have hT : ∀ i, (∀ g : G, g • T i = T i) ∧ v (T i) ≤ 1 := fun i => by
    obtain ⟨h1, h2, -⟩ := trfix _ (hbx i)
    refine ⟨h1, h2 ?_⟩
    rw [map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (hs.b_le i) p) hx1
  choose w hwmem hwle using fun i => hroot (T i) ((memTop _).2 (hT i).1)
  have hwθ : ∀ i, v (T i - w i ^ p) ≤ θ := fun i =>
    le_trans (hwle i) (mul_le_of_le_one_right zero_le' (hT i).2)
  have hw1 : ∀ i, v (w i) ≤ 1 := fun i => by
    have : v (w i ^ p) ≤ 1 := by
      have e : w i ^ p = T i - (T i - w i ^ p) := by ring
      rw [e]
      exact Valuation.map_sub_le v (hT i).2 (le_trans (hwθ i) hθ)
    rw [map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' hp.ne_zero).1 this
  set W : L := ∑ i, a i * w i with hWdef
  have hWmem : W ∈ Fix L N := by
    refine Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hs.a_mem i) ?_
    exact (memN _).2 fun g _ => (memTop _).1 (hwmem i) g
  refine ⟨W, hWmem, ?_⟩

  have key1 : ∑ i, a i ^ p * T i = ∑ q : G ⧸ N, (∑ i, (a i * q.out • b i) ^ p) * q.out • x := by
    simp only [hTdef, cosetTrace, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul', smul_pow', mul_pow]
    ring
  have key2 : c ^ p * x = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) ^ p * q.out • x := by
    rw [Finset.sum_eq_single q₀]
    · rw [hs.sum_in _ ((hout q₀).2 rfl), (memN x).1 hx _ ((hout q₀).2 rfl)]
    · intro q _ hq
      rw [hs.sum_out _ (fun h => hq ((hout q).1 h)), zero_pow hp.ne_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have bound1 : v (c ^ p * x - ∑ i, a i ^ p * T i) ≤ v (p : L) := by
    rw [key1, key2, ← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro q _
    rw [← sub_mul, map_mul]
    have h1 : v (q.out • x) ≤ 1 := by rw [hv]; exact hx1
    have h2 := frob (Fin n) Finset.univ (fun i => a i * q.out • b i)
      (fun i _ => by rw [map_mul, hv]; exact mul_le_one' (hs.a_le i) (hs.b_le i))
    calc _ ≤ v (p : L) * 1 := mul_le_mul' h2 h1
      _ = _ := mul_one _
  have bound2 : v (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) ≤ θ := by
    rw [← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro i _
    rw [← mul_sub, map_mul]
    calc _ ≤ 1 * θ := mul_le_mul' (by rw [map_pow]; exact pow_le_one' (hs.a_le i) p) (hwθ i)
      _ = θ := one_mul θ
  have bound3 : v (∑ i, a i ^ p * w i ^ p - W ^ p) ≤ v (p : L) := by
    have h := frob (Fin n) Finset.univ (fun i => a i * w i)
      (fun i _ => by rw [map_mul]; exact mul_le_one' (hs.a_le i) (hw1 i))
    simp only [mul_pow] at h
    rw [Valuation.map_sub_swap]
    exact h
  have e : c ^ p * x - W ^ p = (c ^ p * x - ∑ i, a i ^ p * T i)
      + (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) + (∑ i, a i ^ p * w i ^ p - W ^ p) := by ring
  rw [e]
  refine Valuation.map_add_le v (Valuation.map_add_le v ?_ ?_) ?_
  · exact le_trans bound1 (le_max_right _ _)
  · exact le_trans bound2 (le_max_left _ _)
  · exact le_trans bound3 (le_max_right _ _)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffHeckeTOperatorGamma1InterGamma0
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem coef_heckeT : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ),
    GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) +
      (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  intro N l q k σ hN hq _ hσ f n
  have hq0 : 0 < q := hq.pos
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.Hk.dia_modularForm N l k (q : ℤ) σ hN hσ f
  have hf := _root_.GlobalTheory.Hk.lev_hasSum_coef N l k hN f
  have hgs := _root_.GlobalTheory.Hk.lev_hasSum_coef N l k hN g
  have hU := GlobalTheory.T.hasSum_heckeUOperatorExplicit q (⇑f) (fun m => GlobalTheory.Hk.coef ⇑f m) hq0 hf
  have hV := GlobalTheory.T.hasSum_heckeVOperatorExplicit q (⇑g) (fun m => GlobalTheory.Hk.coef ⇑g m) hq0 hgs
  have hsum : ∀ τ : ℍ, HasSum (fun m => (GlobalTheory.Hk.coef ⇑f (q * m) +
      (q : ℂ) ^ (k - 1) * (if q ∣ m then GlobalTheory.Hk.coef ⇑g (m / q) else 0)) •
        Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.heckeT k q σ ⇑f τ) := by
    intro τ
    have h2 := (hU τ).add ((hV τ).mul_left ((q : ℂ) ^ (k - 1)))
    have e : GlobalTheory.Hk.heckeT k q σ ⇑f τ =
        GlobalTheory.Hk.uOp q ⇑f τ + (q : ℂ) ^ (k - 1) * GlobalTheory.Hk.vOp q ⇑g τ := by
      rw [hg]; rfl
    rw [e]
    convert h2 using 1 <;> ext m <;> simp only [smul_eq_mul] <;> ring
  rw [_root_.GlobalTheory.Hk.coef_of_hasSum _ _ hsum n, ← hg]

end GlobalTheory.Hk
end

