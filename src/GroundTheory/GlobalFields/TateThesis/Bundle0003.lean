module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.Bundle0001
public import GroundTheory.GlobalFields.Adele.Bundle0001

@[expose] public section

-- bundled from GroundTheory.GlobalFields.TateThesis.ArchCharsUnits
section
namespace GroundTheory.Global

open Complex

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (u : ℂ) :
    (r : ℂ) ^ u = Complex.exp (u * (Real.log r : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le,
    mul_comm]

theorem existsUnique_cpow_of_pos (χ : {x : ℝ // 0 < x} →ₜ* ℂˣ) :
    ∃! s : ℂ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ s := by
  let e : ℝ → {x : ℝ // 0 < x} := fun t => ⟨Real.exp t, Real.exp_pos t⟩
  have econt : Continuous e := Real.continuous_exp.subtype_mk _
  have hlog : ∀ x : {x : ℝ // 0 < x}, e (Real.log x) = x :=
    fun x => Subtype.ext (Real.exp_log x.2)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Subtype.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  refine ⟨s, fun x => ?_, fun s' h' => eq_of_forall_exp_mul_eq fun t => ?_⟩
  · rw [ofReal_cpow_eq_exp x.2, ← hs', hlog]
  · have h1 := h' (e t)
    rw [ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
    rw [← h1, hs']

theorem existsUnique_realUnits (χ : ℝˣ →ₜ* ℂˣ) :
    ∃! p : Fin 2 × ℂ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2 := by
  let e : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
  have econt : Continuous e := Units.isEmbedding_val₀.continuous_iff.mpr Real.continuous_exp
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  have hpos : ∀ (r : ℝ) (hr : 0 < r), (χ (Units.mk0 r hr.ne') : ℂ) = (r : ℂ) ^ s := by
    intro r hr
    have : Units.mk0 r hr.ne' = e (Real.log r) := Units.ext (Real.exp_log hr).symm
    rw [this, hs', ofReal_cpow_eq_exp hr]

  set c : ℂ := (χ (-1) : ℂ) with hc
  have hcc : c * c = 1 := by
    rw [hc, ← Units.val_mul, ← map_mul]
    simp
  let a : Fin 2 := if c = 1 then 0 else 1
  have ha : c = (-1 : ℂ) ^ (a : ℕ) := by
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · simp [a, h]
    · have hne : (-1 : ℂ) ≠ 1 := by norm_num
      simp [a, h, hne]
  have hneg1 : ∀ x : ℝˣ, x = -1 * Units.mk0 (-(x : ℝ)) (neg_ne_zero.mpr x.ne_zero) := by
    intro x
    ext
    simp
  refine ⟨(a, s), fun x => ?_, ?_⟩
  · rcases lt_or_gt_of_ne x.ne_zero with hx | hx
    · conv_lhs => rw [hneg1 x]
      rw [map_mul, Units.val_mul, ← hc, hpos _ (neg_pos.mpr hx), ha, Real.sign_of_neg hx, abs_of_neg hx]
      push_cast
      ring
    · have : x = Units.mk0 (x : ℝ) hx.ne' := by ext; simp
      conv_lhs => rw [this]
      rw [hpos _ hx, Real.sign_of_pos hx, abs_of_pos hx]
      simp
  · rintro ⟨a', s'⟩ h'
    have hs's : s' = s := eq_of_forall_exp_mul_eq fun t => by
      have h1 := h' (e t)
      have he : ((e t : ℝˣ) : ℝ) = Real.exp t := rfl
      rw [he, Real.sign_of_pos (Real.exp_pos t), abs_of_pos (Real.exp_pos t),
        ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
      simp only [Complex.ofReal_one, one_pow, one_mul] at h1
      rw [← h1, hs']
    have ha' : (-1 : ℂ) ^ (a' : ℕ) = (-1 : ℂ) ^ (a : ℕ) := by
      have h1 := h' (-1)
      simp only [Units.val_neg, Units.val_one, abs_neg, abs_one, Complex.ofReal_one,
        Complex.one_cpow, mul_one, Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num)] at h1
      rw [← ha, hc, h1]
      push_cast
      ring
    have haa : a' = a := by
      revert ha'
      generalize a = b
      fin_cases a' <;> fin_cases b <;> norm_num
    simp [haa, hs's]

theorem existsUnique_circle_zpow (χ : Circle →ₜ* ℂˣ) :
    ∃! m : ℤ, ∀ z : Circle, (χ z : ℂ) = (z : ℂ) ^ m := by
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (Circle.exp t))
    (χ.continuous.comp Circle.exp.continuous)
    (fun a b => by simp only [Circle.exp_add, map_mul])
  have hs' : ∀ t : ℝ, (χ (Circle.exp t) : ℂ) = Complex.exp (s * t) := hs

  obtain ⟨n, hn⟩ : ∃ n : ℤ, s = n * I := by
    have h1 : Complex.exp (s * (2 * Real.pi : ℝ)) = 1 := by
      rw [← hs', Circle.exp_two_pi, map_one, Units.val_one]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  have hval : ∀ t : ℝ, (χ (Circle.exp t) : ℂ) = (Circle.exp t : ℂ) ^ n := by
    intro t
    rw [hs', Circle.coe_exp, ← Complex.exp_int_mul, hn]
    congr 1
    ring
  refine ⟨n, fun z => ?_, fun m hm => ?_⟩
  · rw [← Circle.exp_arg z, hval]
  · have hmn : (m : ℂ) * I = n * I := eq_of_forall_exp_mul_eq fun t => by
      have h1 := hm (Circle.exp t)
      rw [hval, Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_int_mul] at h1
      calc Complex.exp (m * I * t) = Complex.exp (m * (t * I)) := by ring_nf
        _ = Complex.exp (n * (t * I)) := h1.symm
        _ = Complex.exp (n * I * t) := by ring_nf
    exact_mod_cast mul_right_cancel₀ I_ne_zero hmn

noncomputable def circleToUnits : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun :=
    Units.isEmbedding_val₀.continuous_iff.mpr (continuous_subtype_val.congr fun _ => rfl)

@[simp] theorem coe_circleToUnits (z : Circle) : ((circleToUnits z : ℂˣ) : ℂ) = z := rfl

theorem existsUnique_complexUnits (χ : ℂˣ →ₜ* ℂˣ) :
    ∃! p : ℤ × ℂ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2 := by

  let e : ℝ → ℂˣ := fun t => Units.mk0 (Real.exp t : ℂ) (by exact_mod_cast (Real.exp_pos t).ne')
  have econt : Continuous e :=
    Units.isEmbedding_val₀.continuous_iff.mpr (Complex.continuous_ofReal.comp Real.continuous_exp)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (by simp [e, Complex.exp_add]))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs

  obtain ⟨n, hn, hnu⟩ := existsUnique_circle_zpow (χ.comp circleToUnits)
  have hn' : ∀ w : Circle, (χ (circleToUnits w) : ℂ) = (w : ℂ) ^ n := hn
  have hnorm : ∀ z : ℂˣ, 0 < ‖(z : ℂ)‖ := fun z => norm_pos_iff.mpr z.ne_zero
  refine ⟨(n, s), fun z => ?_, ?_⟩
  · have hz : z = e (Real.log ‖(z : ℂ)‖) * circleToUnits (Circle.exp (Complex.arg z)) := by
      ext
      rw [Units.val_mul, coe_circleToUnits, Circle.coe_exp]
      show (z : ℂ) = (Real.exp (Real.log ‖(z : ℂ)‖) : ℂ) * _
      rw [Real.exp_log (hnorm z), Complex.norm_mul_exp_arg_mul_I]
    have hw : (Circle.exp (Complex.arg z) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
      rw [Circle.coe_exp, eq_div_iff (by exact_mod_cast (hnorm z).ne'), mul_comm,
        Complex.norm_mul_exp_arg_mul_I]
    conv_lhs => rw [hz]
    rw [map_mul, Units.val_mul, hs', hn', hw, ofReal_cpow_eq_exp (hnorm z), mul_comm]
  · rintro ⟨m, s'⟩ h'
    have hs's : s' = s := eq_of_forall_exp_mul_eq fun t => by
      have h1 := h' (e t)
      have he : ((e t : ℂˣ) : ℂ) = (Real.exp t : ℂ) := rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
        div_self (by exact_mod_cast (Real.exp_pos t).ne'), one_zpow, one_mul,
        ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
      rw [← h1, hs']
    have hmn : m = n := hnu m fun w => by
      have h1 := h' (circleToUnits w)
      rw [coe_circleToUnits, Circle.norm_coe] at h1
      simpa using h1
    simp [hmn, hs's]

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.GaussianComplex
section
namespace GroundTheory.Global

open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal

noncomputable section

def traceFormℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

@[simp] theorem traceFormℂ_apply (z w : ℂ) : traceFormℂ z w = 2 * (z * w).re := by
  simp [traceFormℂ]

def complexPlaceMeasure : Measure ℂ := (2 : ℝ≥0∞) • volume

def complexFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z, 𝐞 (-(2 * (z * w).re)) • f z ∂complexPlaceMeasure

theorem complexFourier_eq_fourierIntegral (f : ℂ → ℂ) :
    complexFourier f =
      VectorFourier.fourierIntegral 𝐞 complexPlaceMeasure traceFormℂ.toLinearMap₁₂ f := by
  funext w
  simp [complexFourier, VectorFourier.fourierIntegral]

def complexGaussian (m : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ m then z ^ m.natAbs else conj z ^ m.natAbs) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)

theorem complexGaussian_zero (z : ℂ) :
    complexGaussian 0 z = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  simp [complexGaussian]

theorem complexFourier_eq_two_mul_fourier (f : ℂ → ℂ) (w : ℂ) :
    complexFourier f w = 2 * 𝓕 f (2 * conj w) := by
  rw [complexFourier, complexPlaceMeasure, integral_smul_measure, fourier_eq]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat]
  congr 2
  funext z
  congr 3
  rw [Complex.inner]
  simp [Complex.mul_re]
  ring

theorem complexFourier_complexGaussian_zero :
    complexFourier (complexGaussian 0) = complexGaussian 0 := by
  funext w
  rw [complexFourier_eq_two_mul_fourier]
  have hb : 0 < ((2 * π : ℝ) : ℂ).re := by simp [Real.pi_pos]
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb (2 * conj w)
  have e : complexGaussian 0 = fun v : ℂ ↦ Complex.exp (-((2 * π : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [complexGaussian_zero]; push_cast; ring_nf
  rw [e, h, Complex.finrank_real_complex]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : ‖2 * conj w‖ = 2 * ‖w‖ := by simp
  rw [hn]
  have h1 : ((π : ℂ) / ((2 * π : ℝ) : ℂ)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2 := by
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one]; push_cast; field_simp
  rw [h1]
  push_cast
  rw [← mul_assoc, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul]
  congr 1
  field_simp

theorem integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k : ℕ) :
    Integrable (fun z : ℂ ↦ ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y : ℝ ↦ y ^ k * Real.exp (-(2 * π) * y ^ 2))).2
  refine h ?_
  rw [Complex.finrank_real_complex]
  have h2 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * π) (by positivity)
    (s := ((k + 1 : ℕ) : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) (k + 1); linarith)
  refine h2.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, smul_eq_mul]
  ring

theorem integrable_norm_pow_smul_complexGaussian (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) := by
  refine (integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k + m.natAbs)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    unfold complexGaussian
    split_ifs <;> fun_prop
  · refine Filter.Eventually.of_forall fun z ↦ ?_
    rw [norm_smul, complexGaussian, norm_mul, norm_exp]
    have : (-2 * π * (‖z‖ : ℂ) ^ 2).re = -(2 * π) * ‖z‖ ^ 2 := by
      rw [← ofReal_pow, ← ofReal_ofNat, ← ofReal_neg, ← ofReal_mul, ← ofReal_mul, ofReal_re]
      ring
    rw [this]
    split_ifs <;> simp [pow_add, mul_assoc]

theorem integrable_norm_pow_smul_complexGaussian' (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) complexPlaceMeasure :=
  (integrable_norm_pow_smul_complexGaussian m k).smul_measure (by simp)

theorem integrable_complexGaussian (m : ℤ) :
    Integrable (complexGaussian m) complexPlaceMeasure := by
  simpa using integrable_norm_pow_smul_complexGaussian' m 0

theorem complexGaussian_mul_zpow {z : ℂ} (hz : z ≠ 0) (m : ℤ) :
    complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) =
      (‖z‖ : ℂ) ^ m.natAbs * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  rw [complexGaussian]
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    simp only [Int.natAbs_natCast, zpow_neg, zpow_natCast, div_pow]
    field_simp
  · obtain ⟨n, hn'⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    subst hn'
    simp only [Int.natAbs_neg, Int.natAbs_natCast, neg_neg, zpow_natCast, div_pow]
    have hc : conj z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm, mul_conj, normSq_eq_norm_sq]; push_cast; ring
    have : conj z ^ n * z ^ n = (‖z‖ : ℂ) ^ n * (‖z‖ : ℂ) ^ n := by
      rw [← mul_pow, hc, ← pow_mul, ← pow_add]; ring_nf
    field_simp
    linear_combination this

theorem integral_comp_norm_complexPlaceMeasure (f : ℝ → ℂ) :
    ∫ z, f ‖z‖ ∂complexPlaceMeasure = 4 * π * ∫ y in Ioi (0 : ℝ), (y : ℂ) * f y := by
  rw [complexPlaceMeasure, integral_smul_measure, integral_fun_norm_addHaar volume f,
    Complex.finrank_real_complex]
  have hb : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [hb]
  simp only [ENNReal.toReal_ofNat, pow_one, Complex.real_smul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.add_one_sub_one]
  push_cast
  ring

theorem integral_complexGaussian_mul_zpow_mul_cpow (m : ℤ) {s : ℂ}
    (hs : 0 < s.re + m.natAbs / 2) :
    ∫ z, complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s /
        ((‖z‖ ^ 2 : ℝ) : ℂ) ∂complexPlaceMeasure =
      π * Gammaℂ (s + m.natAbs / 2) := by
  set n := m.natAbs with hn
  have h : (fun z : ℂ ↦ complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) *
        ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ)) =
      fun z ↦ (fun y : ℝ ↦ (y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) ‖z‖ := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp
    · simp only
      rw [complexGaussian_mul_zpow hz, ofReal_exp, ← hn]
      push_cast
      ring_nf
  rw [h, integral_comp_norm_complexPlaceMeasure (fun y : ℝ ↦ (y : ℂ) ^ n *
    ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ))]
  have ha : 0 < (2 * s + n).re := by simp; linarith
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) =
      mellin (fun t : ℝ ↦ ((Real.exp (-(2 * π * t ^ 2)) : ℝ) : ℂ)) (2 * s + n) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    have e1 : ((y ^ 2 : ℝ) : ℂ) ^ s = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) := by
      rw [cpow_mul_ofReal_nonneg (le_of_lt hy), Real.rpow_two]
    have e2 : (y : ℂ) ^ (2 * s + n - 1) = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) * (y : ℂ) ^ n / y := by
      rw [cpow_sub _ _ hy0, cpow_add _ _ hy0, cpow_natCast, cpow_one]; push_cast; ring
    rw [e1, e2, smul_eq_mul]
    push_cast
    field_simp
  rw [this, mellin_exp_neg_mul_sq (by positivity) ha, Gammaℂ_def]
  have e3 : (2 * s + n) / 2 = s + n / 2 := by ring
  rw [e3]
  push_cast
  ring

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.TracePairing
section
namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun x := ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem mixedTrace_apply (x : mixedSpace K) :
    mixedTrace K x = ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re := rfl

theorem mixedTrace_mixedEmbedding (x : K) :
    mixedTrace K (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  have h1 : ((Algebra.trace ℚ K x : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x))
    rw [Complex.re_sum] at h
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => (φ x).re)
      (fun σ => (σ x).re) (fun _ => rfl)]
    simpa using h
  have h2 : ∀ φ : K →+* ℂ, (φ x).re = ((mk φ).embedding x).re := by
    intro φ
    rcases embedding_mk_eq φ with h | h <;> rw [h]
    simp [ComplexEmbedding.conjugate_coe_eq]
  have h3 : ∀ w : InfinitePlace K,
      ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => mk φ = w), (φ x).re =
        mult w * (w.embedding x).re := by
    intro w
    rw [Finset.sum_congr rfl (fun φ hφ => by rw [h2, (Finset.mem_filter.mp hφ).2]),
      Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [h1, ← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => mk φ) (fun φ => (φ x).re)]
  simp_rw [h3]
  rw [sum_eq_sum_add_sum, mixedTrace_apply]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal,
      ← embedding_of_isReal_apply w.2, Complex.ofReal_re]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex]
    norm_num

def mixedTraceForm : LinearMap.BilinForm ℝ (mixedSpace K) :=
  (LinearMap.mul ℝ (mixedSpace K)).compr₂ (mixedTrace K)

theorem mixedTraceForm_apply (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTrace K (x * y) := rfl

theorem mixedTraceForm_apply' (x y : mixedSpace K) :
    mixedTraceForm K x y = ∑ w, x.1 w * y.1 w + ∑ w, 2 * (x.2 w * y.2 w).re := rfl

theorem mixedTraceForm_comm (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTraceForm K y x := by
  rw [mixedTraceForm_apply, mixedTraceForm_apply, mul_comm]

theorem mixedTraceForm_mixedEmbedding (a b : K) :
    mixedTraceForm K (mixedEmbedding K a) (mixedEmbedding K b) = (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [mixedTraceForm_apply, ← map_mul, mixedTrace_mixedEmbedding]

theorem mixedTraceForm_separatingLeft : (mixedTraceForm K).SeparatingLeft := by
  intro x hx
  have h := hx (x.1, fun w => conj (x.2 w))
  rw [mixedTraceForm_apply'] at h
  simp only [Complex.mul_conj, Complex.ofReal_re] at h
  have h1 : 0 ≤ ∑ w, x.1 w * x.1 w := Finset.sum_nonneg fun w _ => mul_self_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (x.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _)
  have e1 : ∑ w, x.1 w * x.1 w = 0 := by linarith
  have e2 : ∑ w, 2 * Complex.normSq (x.2 w) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg _)] at e1
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _))] at e2
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simpa using e1 w (Finset.mem_univ _)
  · simpa using e2 w (Finset.mem_univ _)

theorem mixedTraceForm_nondegenerate : (mixedTraceForm K).Nondegenerate :=
  ⟨mixedTraceForm_separatingLeft K, fun y hy =>
    mixedTraceForm_separatingLeft K y fun x => by rw [mixedTraceForm_comm]; exact hy x⟩

end

end GroundTheory.Global
end

