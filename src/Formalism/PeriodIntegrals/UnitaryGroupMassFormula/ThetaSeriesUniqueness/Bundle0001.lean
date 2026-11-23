module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.Complete

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.CoefShift
section
noncomputable section

namespace PI.SSU

open Complex

theorem coef_shift (hS : ShiftInv) (f : ℂ → ℂ) (τ K : ℂ) (k : ℤ) (hf : Differentiable ℂ f)
    (h1 : ∀ u, f (u + 1) = f u)
    (hτ : ∀ u, f (u + τ) = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * k * u)) * f u) (n : ℤ) :
    coef f n = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * τ)) * coef f (n + k) := by
  rw [← hS f hf h1 τ n, ← hS f hf h1 0 (n + k), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [hτ, add_zero]
  have e : cexp (-(2 * (Real.pi : ℂ) * I * k * x)) * cexp (-(2 * (Real.pi : ℂ) * I * n * (x + τ))) =
      cexp (-(2 * (Real.pi : ℂ) * I * n * τ)) * cexp (-(2 * (Real.pi : ℂ) * I * ((n + k : ℤ) : ℂ) * x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (K * f x) * e

theorem key_of (hS : ShiftInv) (hC : Complete) : KeyP := by
  intro f τ K k hf hK hk h1 hτ h0
  apply hC f hf h1
  have hrel : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + k) = 0 := by
    intro n
    rw [coef_shift hS f τ K k hf h1 hτ n, mul_eq_zero,
      or_iff_right (mul_ne_zero hK (Complex.exp_ne_zero _))]
  have H : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + 1) = 0 := by
    intro n
    rcases hk with rfl | rfl
    · exact hrel n
    · have := hrel (n + 1)
      rw [show n + 1 + -1 = n by ring] at this
      exact this.symm
  intro n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i hi => exact (H i).mp hi
  | pred i hi =>
    have := H (-(i:ℤ) - 1)
    rw [show -(i:ℤ) - 1 + 1 = -i by ring] at this
    exact this.mpr hi

end PI.SSU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SiegelSetCompleteness
section
noncomputable section

namespace PI.SSU

open Complex Filter Topology

theorem siegel_set_completeness : Complete := by
  intro f hf hper hcoef
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hpr : Function.Periodic (fun x : ℝ => f x) 1 := fun x => by
    simpa using hper (x : ℂ)
  have hcont : Continuous (fun x : ℝ => f x) := hf.continuous.comp Complex.continuous_ofReal
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hpr.lift, by
    first
      | exact continuous_coinduced_dom.mpr hcont
      | exact hcont.quotient_liftOn' _
      | exact (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hcont⟩
  have hF : ∀ x : ℝ, F x = f x := fun x => rfl
  have hcF : ∀ n : ℤ, fourierCoeff F n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have h1 : ∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) • F x = coef f n := by
      unfold coef
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [fourier_coe_apply, hF, smul_eq_mul]
      push_cast
      ring_nf
    rw [h1, hcoef n, smul_zero]
  have hL : ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F = 0 := by
    have hs := hasSum_fourier_series_L2 (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F)
    simp only [fourierCoeff_toLp, hcF, zero_smul] at hs
    exact hs.unique hasSum_zero
  have hF0 : F = 0 := by
    first
      | exact ContinuousMap.toLp_injective AddCircle.haarAddCircle (hL.trans (map_zero _).symm)
      | exact ContinuousMap.toLp_injective (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ)
          (hL.trans (map_zero _).symm)
  have hreal : ∀ x : ℝ, f x = 0 := fun x => by
    have := DFunLike.congr_fun hF0 (x : AddCircle (1 : ℝ))
    rwa [hF, ContinuousMap.zero_apply] at this
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [Function.comp_def] using this
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).ne'
    exact ht.frequently (Frequently.of_forall fun n => hreal _)
  funext z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0)
    hfreq (Set.mem_univ z)

end PI.SSU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SiegelSetShiftInvariance
section
noncomputable section

namespace PI.SSU

open Complex

theorem siegel_set_shift_invariance : ShiftInv := by
  intro f hf hper w n
  set g : ℂ → ℂ := fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)) with hg
  have hgd : Differentiable ℂ g := by
    show Differentiable ℂ (fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)))
    exact hf.mul (by fun_prop)

  have hgp : ∀ z, g (z + 1) = g z := by
    intro z
    show f (z + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (z + 1))) =
      f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z))
    rw [hper z]
    congr 1
    rw [show -(2 * (Real.pi : ℂ) * I * n * (z + 1)) =
        -(2 * (Real.pi : ℂ) * I * n * z) + -((n : ℂ) * (2 * Real.pi * I)) by ring,
      Complex.exp_add, Complex.exp_neg ((n : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, inv_one, mul_one]

  have hvert : ∀ b : ℝ, ∫ x in (0 : ℝ)..1, g (x + b * I) = ∫ x in (0 : ℝ)..1, g x := by
    intro b
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g 0 (1 + b * I)
      hgd.differentiableOn
    have h1 : ((1 : ℂ) + b * I).re = 1 := by simp
    have h2 : ((1 : ℂ) + b * I).im = b := by simp
    rw [h1, h2, Complex.zero_re, Complex.zero_im] at hrect
    have hs : (fun y : ℝ => g (((1 : ℝ) : ℂ) + y * I)) = fun y : ℝ => g (((0 : ℝ) : ℂ) + y * I) := by
      funext y
      rw [← hgp (((0 : ℝ) : ℂ) + y * I)]
      congr 1
      push_cast
      ring
    rw [hs, add_sub_cancel_right, sub_eq_zero] at hrect
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hrect
    exact hrect.symm

  have hH : Function.Periodic (fun y : ℝ => g (y + w.im * I)) 1 := by
    intro y
    show g (((y + 1 : ℝ) : ℂ) + w.im * I) = g ((y : ℂ) + w.im * I)
    rw [← hgp ((y : ℂ) + w.im * I)]
    congr 1
    push_cast
    ring
  have hw : ∀ x : ℝ, (x : ℂ) + w = ((x + w.re : ℝ) : ℂ) + w.im * I := by
    intro x
    apply Complex.ext <;> simp
  calc ∫ x in (0 : ℝ)..1, f (x + w) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (x + w)))
      = ∫ x in (0 : ℝ)..1, (fun y : ℝ => g (y + w.im * I)) (x + w.re) := by
        congr 1
        funext x
        show g ((x : ℂ) + w) = g (((x + w.re : ℝ) : ℂ) + w.im * I)
        rw [hw x]
    _ = ∫ x in (0 + w.re)..(1 + w.re), (fun y : ℝ => g (y + w.im * I)) x :=
        intervalIntegral.integral_comp_add_right (fun y : ℝ => g (y + w.im * I)) w.re
    _ = ∫ x in (0 : ℝ)..(0 + 1), (fun y : ℝ => g (y + w.im * I)) x := by
        rw [zero_add w.re, add_comm 1 w.re]
        exact hH.intervalIntegral_add_eq w.re 0
    _ = ∫ x in (0 : ℝ)..1, g (x + w.im * I) := by rw [zero_add]
    _ = ∫ x in (0 : ℝ)..1, g x := hvert w.im
    _ = coef f n := rfl

end PI.SSU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.ZeroOfCoef
section
noncomputable section

namespace PI.SSU

open Complex

theorem normF_one (a A l p : ℂ) (F : ℂ → ℂ) (hl : Complex.exp l = p) (hF : FE A a p F) (u : ℂ) :
    normF a A l F (u + 1) = normF a A l F u := by
  unfold normF
  have h1 := hF (a * u)
  have e1 : a * (u + 1) = a * u + a := by ring
  rw [e1]
  have hF' : F (a * u + a) = p * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) * (starRingEnd ℂ) a / A -
      (Real.pi : ℂ) * a * (starRingEnd ℂ) a / (2 * A))) := by
    rw [← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hF', ← hl]
  have key : ∀ (P e1 e2 e3 e4 : ℂ), e1 + e2 + e3 = e4 →
      Complex.exp e1 * P * Complex.exp e2 * Complex.exp e3 = P * Complex.exp e4 := by
    intro P e1 e2 e3 e4 h
    rw [← h, Complex.exp_add, Complex.exp_add]
    ring
  apply key
  ring

theorem normF_tau (a b τ A l q : ℂ) (F : ℂ → ℂ) (hτ : a * τ = b) (hF : FE A b q F) (u : ℂ) :
    normF a A l F (u + τ) = (q * Complex.exp (cst a b τ A l)) *
      Complex.exp ((Real.pi : ℂ) / A * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) * u) *
      normF a A l F u := by
  unfold normF
  subst hτ
  have h1 := hF (a * u)
  have e1 : a * (u + τ) = a * u + a * τ := by ring
  rw [e1]
  have hF' : F (a * u + a * τ) = q * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) *
      (starRingEnd ℂ) (a * τ) / A - (Real.pi : ℂ) * (a * τ) * (starRingEnd ℂ) (a * τ) / (2 * A))) := by
    rw [← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hF']
  unfold cst
  have key : ∀ (qq P e1 e2 e3 e4 e5 : ℂ), e1 + e2 = e3 + e4 + e5 →
      qq * P * Complex.exp e1 * Complex.exp e2 = qq * Complex.exp e3 * Complex.exp e4 * (P * Complex.exp e5) := by
    intro qq P e1 e2 e3 e4 e5 h
    have h2 : Complex.exp e1 * Complex.exp e2 = Complex.exp e3 * Complex.exp e4 * Complex.exp e5 := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination (qq * P) * h2
  apply key
  simp only [map_mul]
  ring

theorem normF_diff (a A l : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (normF a A l F) := by
  unfold normF
  fun_prop

theorem coef_lin (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g) (α β : ℂ) (n : ℤ) :
    coef (fun u => α * f u - β * g u) n = α * coef f n - β * coef g n := by
  unfold coef
  have hf' : IntervalIntegrable (fun x : ℝ => f x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg' : IntervalIntegrable (fun x : ℝ => g x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hf'.const_mul α) (hg'.const_mul β)]
  congr 1
  funext x
  ring

theorem zero_of_coef (hK : KeyP) (a b A p q : ℂ) (k : ℤ) (ha : a ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hk1 : k = 1 ∨ k = -1)
    (hk : (Real.pi : ℂ) / A * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * (Real.pi : ℂ) * I * k))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (hFa : FE A a p F) (hFb : FE A b q F)
    (h0 : coef (normF a A (Complex.log p) F) 0 = 0) : F = 0 := by
  have hl : Complex.exp (Complex.log p) = p := Complex.exp_log hp
  have hτ : a * (b / a) = b := by field_simp
  have hN := hK (normF a A (Complex.log p) F) (b / a) (q * Complex.exp (cst a b (b / a) A (Complex.log p))) k
    (normF_diff _ _ _ F hF) (mul_ne_zero hq (Complex.exp_ne_zero _)) hk1
    (normF_one a A _ p F hl hFa)
    (fun u => by
      rw [normF_tau a b (b / a) A _ q F hτ hFb u, hk]
      congr 2; ring_nf) h0
  funext z
  have := congrFun hN (z / a)
  simp only [normF, Pi.zero_apply, mul_div_cancel₀ z ha, mul_eq_zero, Complex.exp_ne_zero, or_false]
    at this
  simpa using this

open Classical in
theorem main_of (hK : KeyP) (hA : AreaLat) : SigmaStarUniq := by
  intro a b hs G G' hG hG'
  have harea : area (lat2 a b) = |((starRingEnd ℂ) a * b).im| := (hA a b hs).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at hs
  have hma : a ∈ lat2 a b := AddSubgroup.subset_closure (by simp)
  have hmb : b ∈ lat2 a b := AddSubgroup.subset_closure (by simp)
  have hp0 : (if a / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  have hq0 : (if b / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  have hz : a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b =
      -(2 * I * ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp <;> ring
  obtain ⟨k, hk1, hk⟩ : ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      (Real.pi : ℂ) / ((area (lat2 a b) : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
        -(2 * (Real.pi : ℂ) * I * k) := by
    rw [harea, hz]
    have hs' : ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_of_neg hneg]; push_cast; field_simp
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [abs_of_pos hpos]; push_cast; field_simp
  have FE_of : ∀ F : ℂ → ℂ, (∀ ω ∈ lat2 a b, ∀ z, U1 (lat2 a b) ω F z =
      (if ω / 2 ∈ lat2 a b then 1 else -1) * F z) →
      FE ((area (lat2 a b) : ℝ) : ℂ) a (if a / 2 ∈ lat2 a b then 1 else -1) F ∧
      FE ((area (lat2 a b) : ℝ) : ℂ) b (if b / 2 ∈ lat2 a b then 1 else -1) F :=
    fun F h => ⟨fun z => h a hma z, fun z => h b hmb z⟩
  obtain ⟨hGa, hGb⟩ := FE_of G hG.2.2.2
  obtain ⟨hG'a, hG'b⟩ := FE_of G' hG'.2.2.2
  have Z := zero_of_coef hK a b _ _ _ k ha0 hp0 hq0 hk1 hk
  set c : (ℂ → ℂ) → ℂ := fun F => coef (normF a ((area (lat2 a b) : ℝ) : ℂ)
    (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) F) 0 with hc
  have hH := Z (fun z => c G * G' z - c G' * G z) (by have := hG.1; have := hG'.1; fun_prop)
    (fun z => by linear_combination c G * hG'a z - c G' * hGa z)
    (fun z => by linear_combination c G * hG'b z - c G' * hGb z)
    (by
      have e : normF a ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1))
          (fun z => c G * G' z - c G' * G z) = fun u => c G * normF a ((area (lat2 a b) : ℝ) : ℂ)
            (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) G' u - c G' * normF a
            ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) G u := by
        funext u; simp only [normF]; ring
      rw [e, coef_lin _ _ (normF_diff _ _ _ _ hG'.1).continuous (normF_diff _ _ _ _ hG.1).continuous]
      simp only [hc]; ring)
  have e : (fun z => c G * G' z) = (fun z => c G' * G z) :=
    funext fun z => sub_eq_zero.1 (congrFun hH z)
  have hd := congrArg (fun F => deriv F 0) e
  rw [deriv_const_mul _ (hG'.1 0), deriv_const_mul _ (hG.1 0), hG.2.1, hG'.2.1] at hd
  by_cases h0 : c G = 0
  · exfalso
    have hG0 := Z G hG.1 hGa hGb h0
    have := hG.2.1
    rw [hG0] at this
    simp at this
  · funext z
    have := congrFun e z
    simp only [mul_one] at hd
    rw [← hd] at this
    exact (mul_left_cancel₀ h0 this).symm

end PI.SSU
end
end

