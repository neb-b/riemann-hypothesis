module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

noncomputable section

theorem pderiv_comm_two_variables (i j : Fin 2) (P : MvPolynomial (Fin 2) ℝ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [pderiv_mul, map_add (f := _), hp, pderiv_X, Pi.single_apply]
    split_ifs <;> (try simp) <;> ring

theorem hasDerivAt_eval_fst (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![u, t] P) (eval ![s, t] (pderiv 0 P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![u, t] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 0 (X n))) s := by
      fin_cases n
      · simpa using hasDerivAt_id' s
      · simpa using hasDerivAt_const s t
    simp only [map_mul, eval_X, pderiv_mul, map_add (f := _)]
    exact hp.mul hX

theorem hasDerivAt_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![s, u] P) (eval ![s, t] (pderiv 1 P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![s, u] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 1 (X n))) t := by
      fin_cases n
      · simpa using hasDerivAt_const t s
      · simpa using hasDerivAt_id' t
    simp only [map_mul, eval_X, pderiv_mul, map_add (f := _)]
    exact hp.mul hX

theorem continuous_eval_fst (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    Continuous fun u => eval ![u, t] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_fst P u t).continuousAt

theorem continuous_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s : ℝ) :
    Continuous fun u => eval ![s, u] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_snd P s u).continuousAt

theorem integral_eval_pderiv_fst (P : MvPolynomial (Fin 2) ℝ) (t a b : ℝ) :
    ∫ u in a..b, eval ![u, t] (pderiv 0 P) = eval ![b, t] P - eval ![a, t] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_fst P u t)
    ((continuous_eval_fst _ t).intervalIntegrable a b)

theorem integral_eval_pderiv_snd (P : MvPolynomial (Fin 2) ℝ) (s a b : ℝ) :
    ∫ u in a..b, eval ![s, u] (pderiv 1 P) = eval ![s, b] P - eval ![s, a] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_snd P s u)
    ((continuous_eval_snd _ s).intervalIntegrable a b)

theorem gKernel_eval_diag (k : ℕ) (c : ℝ) : eval ![c, c] (gKernel ℝ k) = 0 := by
  unfold gKernel
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j < k := Finset.mem_range.1 hj
  have h : 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * j + (2 * k - 2 * j) := by omega
  rw [← pow_add, ← pow_add, h, sub_self]

theorem GHatIdentity.proof (h0 : GKernelIdentity.Statement) : GHatIdentity.Statement := by
  intro k
  obtain ⟨-, -, h11, hmm, h1m, hm1, hc⟩ := h0 ℝ k
  set G := gKernel ℝ k with hGdef
  have hg : gMixed k = pderiv 0 (pderiv 1 G) := rfl
  have hg' : gMixed k = pderiv 1 (pderiv 0 G) := by rw [hg, pderiv_comm_two_variables]
  have hI1 : ∀ t : ℝ, ∫ x in (-1 : ℝ)..1, eval ![x, t] (gMixed k) =
      eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G) := fun t => by
    rw [hg]; exact integral_eval_pderiv_fst _ _ _ _
  have hI2 : ∀ s : ℝ, ∫ y in (-1 : ℝ)..1, eval ![s, y] (gMixed k) =
      eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G) := fun s => by
    rw [hg']; exact integral_eval_pderiv_snd _ _ _ _
  have hsq : squareMean (gMixed k) = k := by
    unfold squareMean
    simp only [hI2]
    rw [intervalIntegral.integral_sub ((continuous_eval_fst _ _).intervalIntegrable _ _)
      ((continuous_eval_fst _ _).intervalIntegrable _ _), integral_eval_pderiv_fst,
      integral_eval_pderiv_fst, h11, hmm, h1m, hm1]
    ring
  refine ⟨hsq, fun c => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hc c
  have hdiag := gKernel_eval_diag k c
  rw [← hGdef] at hdiag
  unfold doublyCentred
  simp only [hI1, hI2, hsq]
  have hin : ∀ s : ℝ, ∫ t in (-1 : ℝ)..c,
      (eval ![s, t] (gMixed k) - 1 / 2 * (eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G)) -
        1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) + (k : ℝ)) =
      (eval ![s, c] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) -
        1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) -
        (c + 1) * (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) := by
    intro s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => eval ![s, t] (pderiv 0 G) - 1 / 2 * (eval ![1, t] G - eval ![-1, t] G) -
        (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) * t)]
    · ring
    · intro t _
      have := ((hasDerivAt_eval_snd (pderiv 0 G) s t).sub
        (((hasDerivAt_eval_snd G 1 t).sub (hasDerivAt_eval_snd G (-1) t)).const_mul (1 / 2))).sub
        ((hasDerivAt_id t).const_mul
          (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k))
      convert this using 1
      · funext u; simp only [Pi.sub_apply, id]
      · rw [hg']; ring
    · exact (((continuous_eval_snd _ s).sub (continuous_const.mul
        ((continuous_eval_snd _ 1).sub (continuous_eval_snd _ (-1))))).sub
        continuous_const |>.add continuous_const).intervalIntegrable _ _
  simp only [hin]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => eval ![s, c] G - eval ![s, -1] G -
      1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) * s -
      (c + 1) * (1 / 2 * (eval ![s, 1] G - eval ![s, -1] G) - k * s))]
  · linear_combination (1 / 2 : ℝ) * e1 + (1 / 2 : ℝ) * e2 - (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e4 +
      hdiag + (1 + c) / 2 * h1m - c * hmm + (1 + c) / 2 * hm1
  · intro s _
    have := (((hasDerivAt_eval_fst G s c).sub (hasDerivAt_eval_fst G s (-1))).sub
      ((hasDerivAt_id s).const_mul
        (1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G))))).sub
      ((((hasDerivAt_eval_fst G s 1).sub (hasDerivAt_eval_fst G s (-1))).const_mul (1 / 2)).sub
        ((hasDerivAt_id s).const_mul (k : ℝ)) |>.const_mul (c + 1))
    convert (preTransparency := .reducible) this using 1
    · funext u
      simp only [Pi.sub_apply, id]
    · ring
  · exact ((((continuous_eval_fst _ c).sub (continuous_eval_fst _ (-1))).sub continuous_const).sub
      (continuous_const.mul ((continuous_const.mul ((continuous_eval_fst _ 1).sub
        (continuous_eval_fst _ (-1)))).sub continuous_const))).intervalIntegrable _ _

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

def kernelSum {S : Type*} [CommRing S] (a b : S) (k : ℕ) : S :=
  ∑ j ∈ range k, (a ^ (2 * j + 1) * b ^ (2 * k - 1 - 2 * j) - a ^ (2 * j) * b ^ (2 * k - 2 * j))

section kernelSum

variable {S : Type*} [CommRing S]

theorem kernelSum_zero (a b : S) : kernelSum a b 0 = 0 := by
  simp [kernelSum]

theorem kernelSum_succ (a b : S) (k : ℕ) :
    kernelSum a b (k + 1) =
      b ^ 2 * kernelSum a b k + (a ^ (2 * k + 1) * b - a ^ (2 * k) * b ^ 2) := by
  unfold kernelSum
  rw [sum_range_succ, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    have hj : j < k := mem_range.mp hj
    rw [show 2 * (k + 1) - 1 - 2 * j = (2 * k - 1 - 2 * j) + 2 by omega,
      show 2 * (k + 1) - 2 * j = (2 * k - 2 * j) + 2 by omega, pow_add, pow_add]
    ring
  · rw [show 2 * (k + 1) - 1 - 2 * k = 1 by omega, show 2 * (k + 1) - 2 * k = 2 by omega, pow_one]

theorem add_mul_kernelSum (a b : S) (k : ℕ) :
    (a + b) * kernelSum a b k = b * (a ^ (2 * k) - b ^ (2 * k)) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
    linear_combination b ^ 2 * ih

theorem map_kernelSum {T : Type*} [CommRing T] (φ : S →+* T) (a b : S) (k : ℕ) :
    φ (kernelSum a b k) = kernelSum (φ a) (φ b) k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [kernelSum, map_sum, map_sub, map_mul, map_pow]

theorem kernelSum_one_one (k : ℕ) : kernelSum (1 : S) 1 k = 0 := by
  simp [kernelSum]

theorem neg_one_pow_two_mul (k : ℕ) : (-1 : S) ^ (2 * k) = 1 := by
  rw [pow_mul]
  simp

theorem kernelSum_neg_one_neg_one (k : ℕ) : kernelSum (-1 : S) (-1) k = 0 := by
  induction k with
  | zero => exact kernelSum_zero _ _
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    ring

theorem kernelSum_one_neg_one (k : ℕ) : kernelSum (1 : S) (-1) k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih]
    push_cast
    ring

theorem kernelSum_neg_one_one (k : ℕ) : kernelSum (-1 : S) 1 k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    push_cast
    ring

end kernelSum

theorem gKernel_eq_kernelSum (R : Type*) [CommRing R] (k : ℕ) :
    gKernel R k = kernelSum (X 0 : MvPolynomial (Fin 2) R) (X 1) k := rfl

theorem eval_gKernel {R : Type*} [CommRing R] (k : ℕ) (a b : R) :
    eval ![a, b] (gKernel R k) = kernelSum a b k := by
  rw [gKernel_eq_kernelSum, map_kernelSum]
  simp

theorem gKernel_isHomogeneous (R : Type*) [CommRing R] (k : ℕ) :
    (gKernel R k).IsHomogeneous (2 * k) := by
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj : j < k := mem_range.mp hj
  refine IsHomogeneous.sub ?_ ?_
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j + 1)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 1 - 2 * j))
    rwa [show 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * k by omega] at h
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 2 * j))
    rwa [show 2 * j + (2 * k - 2 * j) = 2 * k by omega] at h

theorem GKernelIdentity.proof : GKernelIdentity.Statement := by
  intro R _ k
  refine ⟨?_, gKernel_isHomogeneous R k, ?_, ?_, ?_, ?_, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [gKernel_eq_kernelSum, add_mul_kernelSum]
  · rw [eval_gKernel, kernelSum_one_one]
  · rw [eval_gKernel, kernelSum_neg_one_neg_one]
  · rw [eval_gKernel, kernelSum_one_neg_one]
  · rw [eval_gKernel, kernelSum_neg_one_one]
  · have h := add_mul_kernelSum c (-1 : R) k
    rw [eval_gKernel, mul_comm]
    rw [neg_pow, pow_mul] at h
    rw [show c + -1 = c - 1 by ring] at h
    rw [h, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (-1 : R) c k
    rw [eval_gKernel, mul_comm, show c - 1 = -1 + c by ring, h, pow_mul, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (1 : R) c k
    rw [eval_gKernel, mul_comm, h]
    simp
  · have h := add_mul_kernelSum c (1 : R) k
    rw [eval_gKernel, mul_comm, h]
    simp

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Real
open scoped InnerProductSpace

theorem norm_circleMap_sub_ofReal_sq (r φ : ℝ) :
    ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos φ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_re, Complex.exp_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem ZonalKernel.proof : ZonalKernel.Statement := by
  intro c₁ h₁ c₂ h₂ hne
  obtain ⟨h₁l, h₁u⟩ := h₁
  obtain ⟨h₂l, h₂u⟩ := h₂
  have hs₁ : Real.sqrt (1 - c₁ ^ 2) ^ 2 = 1 - c₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs₂ : Real.sqrt (1 - c₂ ^ 2) ^ 2 = 1 - c₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) with hBdef
  set A := 1 - c₁ * c₂ with hAdef
  set D := |c₁ - c₂| with hDdef
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hA : 0 ≤ A := by nlinarith
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hABD : A ^ 2 = B ^ 2 + D ^ 2 := by
    rw [hBdef, mul_pow, hs₁, hs₂, hDdef, sq_abs]; ring
  have hAD : 0 < A + D := by linarith
  set r := B / (A + D) with hrdef
  have hr0 : 0 ≤ r := div_nonneg hB hAD.le
  have hBlt : B < A + D := by nlinarith
  have hr1 : r < 1 := (div_lt_one hAD).mpr hBlt
  have key : ∀ φ : ℝ, kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ =
      (1 / 2) * Real.log ((A + D) / 4) + Real.log ‖circleMap 0 1 φ - (r : ℂ)‖ := by
    intro φ
    have hinner : ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = c₁ * c₂ + B * Real.cos φ := by
      simp [spherePoint, PiLp.inner_apply, Fin.sum_univ_three, hBdef]
      ring
    have hne0 : ‖circleMap 0 1 φ - (r : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h
      have := congrArg norm h
      rw [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
      norm_num at this
      linarith
    have hfac : (1 - (c₁ * c₂ + B * Real.cos φ)) / 2 =
        (A + D) / 4 * ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 := by
      rw [norm_circleMap_sub_ofReal_sq, hrdef]
      field_simp
      linear_combination (2 : ℝ) * hABD
    rw [kernelL, hinner, hfac, Real.log_mul (by positivity) (pow_ne_zero 2 hne0), Real.log_pow]
    push_cast
    ring
  simp only [key]
  have hint : IntervalIntegrable (fun φ : ℝ => Real.log ‖circleMap 0 1 φ - (r : ℂ)‖)
      MeasureTheory.volume 0 (2 * π) := circleIntegrable_log_norm_sub_const (a := (r : ℂ)) (c := 0) 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const]
  have havg := circleAverage_log_norm_sub_const₀ (a := (r : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  rw [circleAverage_def, smul_eq_mul] at havg
  have hpi : (2 * π) ≠ 0 := by positivity
  have hsum : A + D = (1 + max c₁ c₂) * (1 - min c₁ c₂) := by
    rcases le_total c₁ c₂ with h | h
    · rw [max_eq_right h, min_eq_left h, hDdef, abs_of_nonpos (by linarith), hAdef]; ring
    · rw [max_eq_left h, min_eq_right h, hDdef, abs_of_nonneg (by linarith), hAdef]; ring
  rw [zonalKernel, ← hsum, mul_add, havg, smul_eq_mul, sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi]
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsSphereLongitude
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def SphereLongitudeCoordinates.Statement : Prop :=
  sphereMeasure.map (fun n : Sphere2 => (n : E3)) =
    (ENNReal.ofReal (4 * Real.pi))⁻¹ •
      (volume.restrict (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ioc 0 (2 * Real.pi))).map
        (fun p : ℝ × ℝ => spherePoint p.1 p.2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalPairing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def ZonalKernelPairing.Statement : Prop :=
  ∀ F H : Polynomial ℝ,
    (1 / 4) * ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂ =
      -(1 / 2) * uniformMean F.eval * uniformMean H.eval -
        (1 / 4) * ∫ c in (-1 : ℝ)..1, centredPrimitive F c * centredPrimitive H c / (1 - c ^ 2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalReduction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

def ZonalHeightReduction.Statement : Prop :=
  ∀ F H : Polynomial ℝ,
    Integrable (fun p : Sphere2 × Sphere2 =>
      kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * F.eval (height p.1) * H.eval (height p.2)) pairMeasure ∧
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * F.eval (height p.1) * H.eval (height p.2)
        ∂pairMeasure =
      (1 / 4) * ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

