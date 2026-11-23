module

public import Formalism.LFunctionBounds.PositivityBound
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt
public import Formalism.LFunctionBounds.ExpSumLowerBound

@[expose] public section

-- bundled from Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum
section
open Complex Filter Topology

noncomputable section

namespace Formalism.FX


open LFunctionPartialSum in
lemma LFunctionPartialSum.norm_tail_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {B : ℝ}
    (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have K1 : ∀ x : ℝ, 1 ≤ x → ‖(x : ℂ) ^ (-s) - ((x : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hI : Set.uIcc x (x + 1) = Set.Icc x (x + 1) := Set.uIcc_of_le (by linarith)
    have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := by
      rw [hI]
      intro h
      linarith [h.1]
    have hderiv : ∀ t ∈ Set.uIcc x (x + 1),
        HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hr : -s - 1 ≠ -1 := by
        intro h
        apply hs0
        linear_combination -h
      first
      | exact hasDerivAt_ofReal_cpow_const ht0.ne' (neg_ne_zero.mpr hs0)
      | (have h1 := hasDerivAt_ofReal_cpow_const ht0.ne' hr
         have e : -s - 1 + 1 = -s := by ring
         rw [e] at h1
         exact h1)
    have hint : IntervalIntegrable (fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1)) MeasureTheory.volume x (x + 1) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.mul ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr ht0))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have e2 : (x : ℂ) ^ (-s) - ((x : ℂ) + 1) ^ (-s) =
        -(∫ t in x..(x + 1), (-s) * (t : ℂ) ^ (-s - 1)) := by
      rw [hFTC]
      push_cast
      ring
    have hr' : -s.re - 1 ≠ -1 := by
      intro h
      linarith
    have hgi : IntervalIntegrable (fun t : ℝ => ‖s‖ * t ^ (-s.re - 1)) MeasureTheory.volume x (x + 1) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne'))
    rw [e2, norm_neg]
    calc ‖∫ t in x..(x + 1), (-s) * (t : ℂ) ^ (-s - 1)‖
        ≤ ∫ t in x..(x + 1), ‖s‖ * t ^ (-s.re - 1) := by
          refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
            (MeasureTheory.ae_of_all _ (fun t ht => ?_)) hgi
          have ht0 : 0 < t := by linarith [ht.1]
          rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp
      _ = ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hr', h0⟩)]
          have e3 : -s.re - 1 + 1 = -s.re := by ring
          rw [e3]
          have hsr : s.re ≠ 0 := hs.ne'
          field_simp
          ring
  have hterm : ∀ i : ℕ, ‖dterm χ s (i + (N + 1))‖ ≤
      B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    have hx : (1 : ℝ) ≤ ((i + (N + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ i + (N + 1) by omega)
    have h1 := K1 _ hx
    rw [Complex.ofReal_natCast] at h1
    have e : (((i + 1 + (N + 1) : ℕ) : ℝ)) = ((i + (N + 1) : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [e]
    unfold dterm
    rw [norm_mul]
    exact mul_le_mul (hB _) h1 (norm_nonneg _) hB0
  have hf0 : ∀ i : ℕ, 0 ≤ B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    refine mul_nonneg hB0 (mul_nonneg hc (sub_nonneg.mpr ?_))
    have hle : (((i + (N + 1) : ℕ) : ℝ)) ≤ (((i + 1 + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show i + (N + 1) ≤ i + 1 + (N + 1) by omega)
    have hpos : (0 : ℝ) < (((i + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show 0 < i + (N + 1) by omega)
    first
    | exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    | exact Real.rpow_le_rpow_of_exponent_nonpos hpos hle (by linarith)
    | (rw [Real.rpow_neg hpos.le, Real.rpow_neg (hpos.le.trans hle)]
       exact inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hle hs.le))
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
    intro n
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub']
    have hv0 : (((0 + (N + 1) : ℕ) : ℝ)) ^ (-s.re) = ((N : ℝ) + 1) ^ (-s.re) := by
      congr 1
      push_cast
      ring
    rw [hv0]
    have hvn : 0 ≤ (((n + (N + 1) : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hm := mul_nonneg (mul_nonneg hB0 hc) hvn
    nlinarith
  have hsf := summable_of_sum_range_le hf0 hpart
  have hsn : Summable (fun i : ℕ => ‖dterm χ s (i + (N + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsf
  calc ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ ∑' i, ‖dterm χ s (i + (N + 1))‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' i : ℕ, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
      first
      | exact Summable.tsum_le_tsum hterm hsn hsf
      | exact tsum_le_tsum hterm hsn hsf
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := Real.tsum_le_of_sum_range_le hf0 hpart

open LFunctionPartialSum in
theorem l_function_partial_sum : LPartialSum := by
  intro q _ χ hχ B hB s hs N hN
  have hB' : ∀ M, ‖Ap χ M‖ ≤ B := hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  rw [LFunction_eq_G χ hχ hB' hs, ← partial_identity χ s N]
  have hsum := summable_dterm χ hB' hs
  have hG : LFunctionPartialSum.G χ s = ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm χ s n + Ap χ N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le χ hB' hs N
  have h2 : ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB' N) (Real.rpow_nonneg (by positivity) _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ((N : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by linarith) (by linarith)
  have hq : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  have h5 : 0 ≤ ((N : ℝ) + 1) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  calc ‖∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm χ s (i + (N + 1))‖ + ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring
    _ ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (by linarith))
    _ ≤ 2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have : 0 ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
          mul_nonneg (mul_nonneg hB0 (by linarith)) h4
        linarith

end Formalism.FX
end
end

-- bundled from Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue
section
open Complex

noncomputable section

namespace Formalism.FX

theorem rectRes_ftc_log {γ : ℝ → ℂ} {d : ℂ} {a b : ℝ} (hγ : ∀ t, HasDerivAt γ d t)
    (hs : ∀ t ∈ Set.uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, d / γ t = log (γ b) - log (γ a) := by
  have hc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hγ t).clog_real (hs t ht)) ?_
  refine ContinuousOn.intervalIntegrable ?_
  exact continuousOn_const.div hc.continuousOn fun t ht => Complex.slitPlane_ne_zero (hs t ht)

theorem rectRes_log_sub_log_neg_of_im_pos {z : ℂ} (h : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  have h1 := Complex.arg_neg_eq_arg_sub_pi_of_im_pos h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

theorem rectRes_log_sub_log_neg_of_im_neg {z : ℂ} (h : z.im < 0) :
    log z - log (-z) = -((Real.pi : ℂ) * I) := by
  have h1 := Complex.arg_neg_eq_arg_add_pi_of_im_neg h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

theorem rectRes_hasDerivAt_horiz (c : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + c) 1 t := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const c
  simpa using h

theorem rectRes_hasDerivAt_vert (c : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => c + (y : ℂ) * I) I t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add c
  simpa using h

theorem rectInt_inv_sub (p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => 1 / (w - p)) x0 x1 y0 y1 = 2 * (Real.pi : ℂ) * I := by
  have E1 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y0 : ℂ) * I - p) =
      log ((x1 : ℂ) + (y0 : ℂ) * I - p) - log ((x0 : ℂ) + (y0 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y0 : ℂ) * I - p)) (d := 1)
      (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))
    simpa only [add_sub_assoc] using h
  have E2 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y1 : ℂ) * I - p) =
      log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x0 : ℂ) + (y1 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y1 : ℂ) * I - p)) (d := 1)
      (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))
    simpa only [add_sub_assoc] using h
  have E3 : I * ∫ y in y0..y1, 1 / ((x1 : ℂ) + (y : ℂ) * I - p) =
      log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x1 : ℂ) + (y0 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => ((x1 : ℂ) - p) + (y : ℂ) * I) (d := I)
      (a := y0) (b := y1) (fun t => rectRes_hasDerivAt_vert _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul]
    have e1 : (x1 : ℂ) + (y1 : ℂ) * I - p = ((x1 : ℂ) - p) + (y1 : ℂ) * I := by ring
    have e0 : (x1 : ℂ) + (y0 : ℂ) * I - p = ((x1 : ℂ) - p) + (y0 : ℂ) * I := by ring
    rw [e1, e0, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x1 : ℂ) + (y : ℂ) * I - p)) = I / (((x1 : ℂ) - p) + (y : ℂ) * I)
    rw [mul_one_div]
    congr 1
    ring
  have E4 : I * ∫ y in y0..y1, 1 / ((x0 : ℂ) + (y : ℂ) * I - p) =
      log (-((x0 : ℂ) + (y1 : ℂ) * I - p)) - log (-((x0 : ℂ) + (y0 : ℂ) * I - p)) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => -(((x0 : ℂ) - p) + (y : ℂ) * I)) (d := -I)
      (a := y0) (b := y1) (fun t => (rectRes_hasDerivAt_vert _ t).neg)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul]
    have e1 : (x0 : ℂ) + (y1 : ℂ) * I - p = ((x0 : ℂ) - p) + (y1 : ℂ) * I := by ring
    have e0 : (x0 : ℂ) + (y0 : ℂ) * I - p = ((x0 : ℂ) - p) + (y0 : ℂ) * I := by ring
    rw [e1, e0, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x0 : ℂ) + (y : ℂ) * I - p)) = -I / -(((x0 : ℂ) - p) + (y : ℂ) * I)
    rw [neg_div_neg_eq, mul_one_div]
    congr 1
    ring
  have P1 := rectRes_log_sub_log_neg_of_im_pos (z := (x0 : ℂ) + (y1 : ℂ) * I - p)
    (by simp <;> linarith)
  have P0 := rectRes_log_sub_log_neg_of_im_neg (z := (x0 : ℂ) + (y0 : ℂ) * I - p)
    (by simp <;> linarith)
  unfold rectInt
  beta_reduce
  rw [E1, E2, E3, E4]
  linear_combination P1 - P0

theorem rectRes_edge (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (γ : ℝ → ℂ) (a c : ℝ)
    (hγ : Continuous γ) (hG : ContinuousOn (fun t => G (γ t)) (Set.uIcc a c))
    (hP : ∀ t ∈ Set.uIcc a c, ∀ p ∈ P, γ t ≠ p)
    (hg : ∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) :
    ∫ t in a..c, g (γ t) =
      (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
  have hγP : ∀ t ∈ Set.uIcc a c, γ t ∉ P := fun t ht hmem => hP t ht _ hmem rfl
  have hcont : ∀ p ∈ P, ContinuousOn (fun t => 1 / (γ t - p)) (Set.uIcc a c) := fun p hp =>
    continuousOn_const.div (hγ.continuousOn.sub continuousOn_const)
      (fun t ht => sub_ne_zero.2 (hP t ht p hp))
  calc ∫ t in a..c, g (γ t)
      = ∫ t in a..c, (G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        show g (γ t) = G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))
        rw [hg _ (hγP t ht)]
        congr 1
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [mul_one_div]
    _ = (∫ t in a..c, G (γ t)) + ∫ t in a..c, ∑ p ∈ P, b p * (1 / (γ t - p)) := by
        refine intervalIntegral.integral_add hG.intervalIntegrable ?_
        exact (continuousOn_finsetSum P (fun p hp => continuousOn_const.mul (hcont p hp))).intervalIntegrable
    _ = (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
        rw [intervalIntegral.integral_finsetSum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro p hp
          exact ((hcont p hp).intervalIntegrable).const_mul (b p)

theorem rectRes_sum_combo (P : Finset ℂ) (b A B C D : ℂ → ℂ) :
    ∑ p ∈ P, b p * (A p - B p + I * C p - I * D p) =
      ∑ p ∈ P, b p * A p - ∑ p ∈ P, b p * B p + I * ∑ p ∈ P, b p * C p - I * ∑ p ∈ P, b p * D p := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem rectangle_residue : RectResidue := by
  unfold RectResidue
  intro g G P b x0 x1 y0 y1 _ _ hPin hU hg
  obtain ⟨U, -, hsub, hGd⟩ := hU
  have hGc : ContinuousOn G U := hGd.continuousOn
  have hG0 : ((∫ x in x0..x1, G ((x : ℂ) + (y0 : ℂ) * I)) - (∫ x in x0..x1, G ((x : ℂ) + (y1 : ℂ) * I))
      + I * (∫ y in y0..y1, G ((x1 : ℂ) + (y : ℂ) * I))) - I * (∫ y in y0..y1, G ((x0 : ℂ) + (y : ℂ) * I))
      = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨x0, y0⟩ ⟨x1, y1⟩
      (hGd.mono hsub)
    simp only [smul_eq_mul] at h
    exact h
  have eB := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.1]) hg
  have eT := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y1 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.2]) hg
  have eR := rectRes_edge g G P b (fun y : ℝ => (x1 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).2.1]) hg
  have eL := rectRes_edge g G P b (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).1]) hg
  have hc := rectRes_sum_combo P b
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p))
  have hsum : ∑ p ∈ P, b p * ((∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
      - (∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
      + I * (∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
      - I * (∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p)))
      = 2 * (Real.pi : ℂ) * I * ∑ p ∈ P, b p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h := rectInt_inv_sub p x0 x1 y0 y1 (hPin p hp).1 (hPin p hp).2.1 (hPin p hp).2.2.1
      (hPin p hp).2.2.2
    unfold rectInt at h
    beta_reduce at h
    rw [h]
    ring
  unfold rectInt
  linear_combination eB - eT + I * eR - I * eL + hG0 + hsum - hc

end Formalism.FX
end
end

