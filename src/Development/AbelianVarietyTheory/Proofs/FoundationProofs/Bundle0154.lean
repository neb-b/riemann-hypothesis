module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem polyB_summable_norm_mul_pow {a : ℕ → ℂ} (ha : PolyB a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖a n‖ * r ^ n := by
  obtain ⟨C, A, h⟩ := ha
  have hs : Summable fun n : ℕ => C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by
    refine Summable.mul_left _ (Summable.add ?_ ?_)
    · exact summable_pow_mul_geometric_of_norm_lt_one A (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    · exact summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _)) (fun n => ?_) hs
  have hb : ((n : ℝ) + 1) ^ A ≤ 2 ^ A * ((n : ℝ) ^ A + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_add, one_pow]
      have : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (le_refl (0:ℝ)) A]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : ((n : ℝ) + 1) ^ A ≤ (2 * n) ^ A := pow_le_pow_left₀ (by positivity) (by linarith) A
      rw [mul_pow] at this
      nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) A]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) ((h 0).trans (by simp))
  calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 _)
    _ ≤ C * (2 ^ A * ((n : ℝ) ^ A + 1)) * r ^ n := by gcongr
    _ = C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by ring

theorem exists_upperHalfPlane_exp_eq {q : ℂ} (h0 : q ≠ 0) (h1 : ‖q‖ < 1) :
    ∃ τ : ℍ, ∀ n : ℕ, cexp (2 * π * Complex.I * n * τ) = q ^ n := by
  have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have him : 0 < (Complex.log q / (2 * π * Complex.I)).im := by
    have e : Complex.log q / (2 * π * Complex.I) = -Complex.I * Complex.log q / (2 * π) := by
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [e]
    have : (-Complex.I * Complex.log q / (2 * π)).im = - (Complex.log q).re / (2 * π) := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
      simp
    rw [this, Complex.log_re]
    have hl : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr h0) h1
    have : 0 < 2 * π := by positivity
    apply div_pos (by simpa using hl) this
  refine ⟨⟨_, him⟩, fun n => ?_⟩
  have : 2 * π * Complex.I * (n : ℂ) * ((⟨_, him⟩ : ℍ) : ℂ) = n * Complex.log q := by
    field_simp
  rw [this, Complex.exp_nat_mul, Complex.exp_log h0]

theorem qs_injective : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  intro a b ha hb hab
  set c : ℕ → ℂ := fun n => a n - b n with hcdef
  have hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n : ℕ => ‖c n‖ * r ^ n := by
    intro r h0 h1
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg h0 _)) (fun n => ?_)
      ((polyB_summable_norm_mul_pow ha h0 h1).add (polyB_summable_norm_mul_pow hb h0 h1))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg h0 _)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    have := hsum (1 / 2) (by norm_num) (by norm_num)
    refine this.congr (fun n => ?_)
    rw [hp, FormalMultilinearSeries.ofScalars_norm]
    simp
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hval : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → p.sum q = 0 := by
    intro q h0 h1
    obtain ⟨τ, hτ⟩ := exists_upperHalfPlane_exp_eq h0 h1
    have ha' : Summable fun n => a n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow ha (norm_nonneg q) h1)
    have hb' : Summable fun n => b n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow hb (norm_nonneg q) h1)
    have e := congrFun hab τ
    simp only [qs, hτ] at e
    show ∑' n, p n (fun _ => q) = 0
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, hcdef, sub_mul]
    rw [Summable.tsum_sub ha' hb', e, sub_self]
  have hcont : ContinuousAt p.sum 0 := hP.continuousOn.continuousAt (Metric.eball_mem_nhds 0 hpos)
  have h0 : p.sum 0 = 0 := by
    have hev : p.sum =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
        with q hq0 hq1
      exact hval q hq0 (by simpa using hq1)
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
  have hloc : p.sum =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact h0
    · exact hval q hq0 (by simpa using hq)
  have hpz : p = 0 := hP.hasFPowerSeriesAt.eq_zero_of_eventually hloc
  funext n
  have hn : p n = 0 := by rw [hpz]; rfl
  have : c n = 0 := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp hn
  exact sub_eq_zero.mp this

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuous
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qterm_norm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summable_succ_pow_mul_geom (A : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1)
  have hs' : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have := hs'.mul_left r⁻¹
  refine this.congr fun n => ?_
  push_cast
  rw [pow_succ]
  field_simp

theorem qterm_bound {a : ℕ → ℂ} {C : ℝ} {A : ℕ} (hC : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    {y₀ : ℝ} (n : ℕ) (τ : ℍ) (hτ : y₀ ≤ τ.im) :
    ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  rw [norm_mul, qterm_norm]
  have h1 : Real.exp (-2 * π * τ.im) ^ n ≤ Real.exp (-2 * π * y₀) ^ n := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  calc ‖a n‖ * Real.exp (-2 * π * τ.im) ^ n ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * τ.im) ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
        apply mul_le_mul_of_nonneg_left h1
        exact le_trans (norm_nonneg _) (hC n)

theorem qterm_summable_bound {C : ℝ} (A : ℕ) {y₀ : ℝ} (hy : 0 < y₀) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  have h := summable_succ_pow_mul_geom A (r := Real.exp (-2 * π * y₀)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
  simpa [mul_assoc] using h.mul_left C

theorem qs_summable_continuous : ∀ a : ℕ → ℂ, PolyB a →
    (∀ τ : ℍ, Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) ∧ Continuous (qs a) := by
  intro a ⟨C, A, hC⟩
  refine ⟨fun τ => ?_, ?_⟩
  · exact (qterm_summable_bound (C := C) A τ.im_pos).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => qterm_bound hC n τ le_rfl)
  · rw [continuous_iff_continuousAt]
    intro τ₀
    have hy : 0 < τ₀.im / 2 := half_pos τ₀.im_pos
    have hopen : IsOpen {τ : ℍ | τ₀.im / 2 < τ.im} :=
      isOpen_lt continuous_const UpperHalfPlane.continuous_im
    have hmem : τ₀ ∈ {τ : ℍ | τ₀.im / 2 < τ.im} := by
      show τ₀.im / 2 < τ₀.im
      linarith [τ₀.im_pos]
    have hon : ContinuousOn (qs a) {τ : ℍ | τ₀.im / 2 < τ.im} := by
      unfold qs
      refine continuousOn_tsum (fun n => ?_) (qterm_summable_bound (C := C) A hy) ?_
      · apply Continuous.continuousOn
        fun_prop
      · intro n τ hτ
        exact qterm_bound hC n τ (le_of_lt hτ)
    exact hon.continuousAt (hopen.mem_nhds hmem)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

def rowZ (γ : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1)
  invFun x := (x.1 * γ 1 1 - x.2 * γ 1 0, -(x.1 * γ 0 1) + x.2 * γ 0 0)
  left_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h
  right_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h

theorem rowZ_apply (γ : SL(2, ℤ)) (x : ℤ × ℤ) :
    rowZ γ x = (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) := rfl

theorem rowZ_add_smul (γ : SL(2, ℤ)) (x v : ℤ × ℤ) (r : ℤ) :
    rowZ γ (x + r • v) = rowZ γ x + r • rowZ γ v := by
  simp only [rowZ_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.mk_add_mk, Prod.smul_mk]
  ext <;> simp only <;> ring

theorem dif_comp_rowZ (L : ℕ) (γ : SL(2, ℤ)) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (rowZ γ y)) = fun x => dif L (rowZ γ v) F (rowZ γ x) := by
  funext x
  simp only [dif, rowZ_add_smul]

theorem dif_const_mul (L : ℕ) (v : ℤ × ℤ) (c : ℂ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => c * F y) = fun x => c * dif L v F x := by
  funext x
  simp only [dif, ← Finset.mul_sum]
  ring

theorem lat_smul (j L : ℕ) (v : ℤ × ℤ) (Φ Φ' : ℤ × ℤ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ)
    (hΦ : ∀ x : ℤ × ℤ, Φ' (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x) :
    lat j 0 L v Φ (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ j *
      lat j 0 L (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1) Φ' τ := by
  set D : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [UpperHalfPlane.denom, hD] using this
  have hcoe : ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [hD]
  set H : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hH
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) =
      fun y => D ^ j * H (rowZ γ y) := by
    funext y
    simp only [hH, trm, rowZ_apply, hcoe, mul_zero, neg_mul, Real.rpow_zero, Complex.ofReal_one, mul_one]
    have : (y.1 : ℂ) * ((((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D) + y.2 =
        ((((y.1 * γ 0 0 + y.2 * γ 1 0 : ℤ)) : ℂ) * τ + ((y.1 * γ 0 1 + y.2 * γ 1 1 : ℤ) : ℂ)) / D := by
      field_simp
      push_cast
      ring
    rw [this, div_pow, inv_div]
    ring_nf
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) x =
      D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) (rowZ γ x) := by
    intro x
    rw [hG, dif_const_mul, dif_const_mul]
    simp only
    rw [dif_comp_rowZ]
    rw [show (fun x => dif L (rowZ γ v) H (rowZ γ x)) = fun x => (dif L (rowZ γ v) H) (rowZ γ x) from rfl,
      dif_comp_rowZ]
  unfold lat
  simp_rw [hdd]
  have hΦ' : ∀ x, Φ x = Φ' (rowZ γ x) := fun x => (hΦ x).symm
  simp_rw [hΦ']
  rw [Equiv.tsum_eq (rowZ γ) (fun z => Φ' z * (D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) z)),
    ← tsum_mul_left]
  congr 1
  funext x
  rw [hH]
  simp only [rowZ_apply]
  ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrence
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_le_of_bounded_two_step_recursion (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ) (hR : 0 ≤ R)
    (h0 : c 0 = 1) (h1 : c 1 = x + y)
    (hrec : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r)
    (hb : ∀ r, ‖c r‖ ≤ C * R ^ r) : ‖x‖ ≤ R := by
  have hd : ∀ r : ℕ, c (r + 1) - y * c r = x ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [h0, h1]
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by ring]
      linear_combination hrec n + x * ih
  have key : ∀ r : ℕ, ‖x‖ ^ (r + 1) ≤ C * (R + ‖y‖) * R ^ r := by
    intro r
    calc ‖x‖ ^ (r + 1) = ‖c (r + 1) - y * c r‖ := by rw [hd r, norm_pow]
      _ ≤ ‖c (r + 1)‖ + ‖y‖ * ‖c r‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ C * R ^ (r + 1) + ‖y‖ * (C * R ^ r) :=
          add_le_add (hb _) (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
      _ = C * (R + ‖y‖) * R ^ r := by ring
  by_contra hlt
  push_neg at hlt
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hlt
  have hq0 : 0 ≤ R / ‖x‖ := div_nonneg hR hxpos.le
  have hq1 : R / ‖x‖ < 1 := (div_lt_one hxpos).2 hlt
  have ht : Tendsto (fun r : ℕ => C * (R + ‖y‖) * (R / ‖x‖) ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * (R + ‖y‖))
  have hle : ∀ r : ℕ, ‖x‖ ≤ C * (R + ‖y‖) * (R / ‖x‖) ^ r := by
    intro r
    have hpos : 0 < ‖x‖ ^ r := pow_pos hxpos r
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos, ← pow_succ']
    exact key r
  have : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  linarith

theorem roots_norm_le_of_bounded_two_step_recursion :
    ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y →
      (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) →
      ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  intro x y c C R hR h0 h1 hrec hb
  refine ⟨norm_le_of_bounded_two_step_recursion x y c C R hR h0 h1 hrec hb,
    norm_le_of_bounded_two_step_recursion y x c C R hR h0 (by rw [h1, add_comm]) ?_ hb⟩
  intro r
  rw [hrec r]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SecondDifferenceInvPowBound
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.SecondDiff

lemma half_le_norm {z w : ℂ} (hw : ‖w - z‖ ≤ ‖z‖ / 2) : ‖z‖ / 2 ≤ ‖w‖ := by
  have h := norm_sub_norm_le z w
  rw [norm_sub_rev] at h
  linarith

lemma ne_zero_of_near {z w : ℂ} (hz : z ≠ 0) (hw : ‖w - z‖ ≤ ‖z‖ / 2) : w ≠ 0 := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := half_le_norm hw
  intro h0
  rw [h0, norm_zero] at h
  linarith

lemma zpow_neg_lip (n : ℕ) {z u v : ℂ} (hz : z ≠ 0)
    (hu : ‖u - z‖ ≤ ‖z‖ / 2) (hv : ‖v - z‖ ≤ ‖z‖ / 2) :
    ‖u ^ (-(n:ℤ)) - v ^ (-(n:ℤ))‖ ≤ n * (2 / ‖z‖) ^ (n + 1) * ‖u - v‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), ‖w - z‖ ≤ ‖z‖ / 2 := by
    intro w hw; simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 2), HasDerivAt (fun x : ℂ => x ^ (-(n:ℤ)))
      (((-(n:ℤ) : ℤ) : ℂ) * w ^ (-(n:ℤ) - 1)) w :=
    fun w hw => hasDerivAt_zpow _ w (Or.inl (ne_zero_of_near hz (hmem w hw)))
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x : ℂ => x ^ (-(n:ℤ)))
    (s := Metric.closedBall z (‖z‖ / 2)) (x := v) (y := u) (C := n * (2 / ‖z‖) ^ (n + 1))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv]
      have hw' : ‖z‖ / 2 ≤ ‖w‖ := half_le_norm (hmem w hw)
      have hwpos : 0 < ‖w‖ := by linarith
      rw [norm_mul, norm_zpow]
      have e1 : ‖(((-(n:ℤ)) : ℤ) : ℂ)‖ = n := by simp
      have e2 : -(n:ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, zpow_neg, zpow_natCast, ← inv_div, inv_pow]
      gcongr)
    (convex_closedBall z _)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)
  simpa using key

theorem second_diff_inv_pow : ∀ j : ℕ, ∃ C : ℝ, ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ →
    ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖
      ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2) := by
  intro j
  refine ⟨j * (j + 1) * 2 ^ (j + 2), ?_⟩
  intro z a b hz ha hb
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set g : ℂ → ℂ := fun w => w ^ (-(j:ℤ)) - (w + a) ^ (-(j:ℤ)) with hg
  have hmem : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), ‖w - z‖ ≤ ‖z‖ / 2 ∧ ‖w + a - z‖ ≤ ‖z‖ / 2 := by
    intro w hw
    have h : ‖w - z‖ ≤ ‖z‖ / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    refine ⟨by linarith, ?_⟩
    calc ‖w + a - z‖ = ‖(w - z) + a‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖a‖ := norm_add_le _ _
      _ ≤ ‖z‖ / 2 := by linarith
  have hd : ∀ w ∈ Metric.closedBall z (‖z‖ / 4), HasDerivAt g
      ((((-(j:ℤ)) : ℤ) : ℂ) * (w ^ (-(j:ℤ) - 1) - (w + a) ^ (-(j:ℤ) - 1))) w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hmem w hw
    have d1 := hasDerivAt_zpow (-(j:ℤ)) w (Or.inl (ne_zero_of_near hz h1))
    have d2 := (hasDerivAt_zpow (-(j:ℤ)) (w + a) (Or.inl (ne_zero_of_near hz h2))).comp_add_const w a
    rw [mul_sub]
    exact d1.sub d2
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := g)
    (s := Metric.closedBall z (‖z‖ / 4)) (x := z) (y := z + b)
    (C := j * ((j + 1 : ℕ) * (2 / ‖z‖) ^ ((j + 1 : ℕ) + 1) * ‖a‖))
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by
      rw [(hd w hw).deriv, norm_mul]
      obtain ⟨h1, h2⟩ := hmem w hw
      have e1 : ‖(((-(j:ℤ)) : ℤ) : ℂ)‖ = j := by simp
      have e2 : -(j:ℤ) - 1 = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2]
      have L := zpow_neg_lip (j + 1) hz h1 h2
      have e3 : ‖w - (w + a)‖ = ‖a‖ := by rw [sub_add_cancel_left, norm_neg]
      rw [e3] at L
      gcongr)
    (convex_closedBall z _)
    (by simp [Metric.mem_closedBall, dist_eq_norm]; positivity)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using (by linarith : ‖b‖ ≤ ‖z‖ / 4))
  have eq : (z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹ = -(g (z + b) - g z) := by
    simp only [hg, zpow_neg, zpow_natCast]
    rw [show z + b + a = z + a + b by ring]
    ring
  rw [eq, norm_neg]
  refine key.trans (le_of_eq ?_)
  rw [add_sub_cancel_left, div_pow]
  push_cast
  field_simp

end GlobalTheory.EisM.SecondDiff
end

