module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSumEqZero
section
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace GlobalTheory.IntegerUnitBound


open scoped Classical in
theorem exists_unit_norm_add_le (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : logSpace E, ∃ u : (𝓞 E)ˣ,
      ∀ w, |v w + logEmbedding E (Additive.ofMul u) w| ≤ C := by
  classical
  let B := (basisUnitLattice E).ofZLatticeBasis (E := logSpace E) ℝ (unitLattice E)
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun v => ?_⟩

  have hmem : -((ZSpan.floor B v : logSpace E)) ∈ unitLattice E := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice E) (basisUnitLattice E)]
    exact neg_mem (ZSpan.floor B v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨Additive.toMul x, fun w => ?_⟩
  have hsum : v + logEmbedding E (Additive.ofMul (Additive.toMul x)) = ZSpan.fract B v := by
    have hx' : logEmbedding E x = -((ZSpan.floor B v : logSpace E)) := hx
    rw [ofMul_toMul, hx', ZSpan.fract_apply, sub_eq_add_neg]
  calc |v w + logEmbedding E (Additive.ofMul (Additive.toMul x)) w|
      = ‖(v + logEmbedding E (Additive.ofMul (Additive.toMul x))) w‖ := by
        rw [Real.norm_eq_abs, Pi.add_apply]
    _ ≤ ‖v + logEmbedding E (Additive.ofMul (Additive.toMul x))‖ := norm_le_pi_norm _ w
    _ = ‖ZSpan.fract B v‖ := by rw [hsum]
    _ ≤ ∑ i, ‖B i‖ := ZSpan.norm_fract_le B v


open scoped Classical in
theorem exists_unit_of_sum_eq_zero (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ t : InfinitePlace E → ℝ, ∑ w, (mult w : ℝ) * t w = 0 → ∃ u : (𝓞 E)ˣ,
      ∀ w : InfinitePlace E, |t w + Real.log (w (u : E))| ≤ C := by
  classical
  obtain ⟨C₁, hC₁, hC⟩ := exists_unit_norm_add_le E
  refine ⟨Fintype.card (InfinitePlace E) * C₁, fun t ht => ?_⟩
  obtain ⟨u, hu⟩ := hC (fun w => (mult w.1 : ℝ) * t w.1)
  refine ⟨u, ?_⟩

  have hoff : ∀ w : {w : InfinitePlace E // w ≠ w₀},
      |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| ≤ C₁ := by
    intro w
    have h := hu w
    rw [logEmbedding_component] at h
    rwa [mul_add]

  have hone : ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E))| ≤ |(mult w : ℝ) * (t w + Real.log (w (u : E)))| := by
    intro w
    rw [abs_mul, abs_of_pos (Nat.cast_pos.2 mult_pos : (0 : ℝ) < mult w)]
    exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult
  have hcard : C₁ ≤ Fintype.card (InfinitePlace E) * C₁ := by
    have h : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    nlinarith
  intro w
  by_cases hw : w = w₀
  ·
    subst hw
    have htot : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w + Real.log (w (u : E))) = 0 := by
      simp only [mul_add, Finset.sum_add_distrib, ht, sum_mult_mul_log, add_zero]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at htot
    calc |t w₀ + Real.log (w₀ (u : E))|
        ≤ |(mult w₀ : ℝ) * (t w₀ + Real.log (w₀ (u : E)))| := hone w₀
      _ = |∑ w : {w : InfinitePlace E // w ≠ w₀}, (mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| := by
        rw [eq_neg_of_add_eq_zero_left htot, abs_neg]
      _ ≤ ∑ w : {w : InfinitePlace E // w ≠ w₀}, |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : {w : InfinitePlace E // w ≠ w₀}, C₁ := Finset.sum_le_sum fun w _ => hoff w
      _ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * C₁ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card (InfinitePlace E) * C₁ := by
        gcongr
        exact_mod_cast Fintype.card_subtype_le _
  · exact (hone w).trans ((hoff ⟨w, hw⟩).trans hcard)

theorem exists_unit_int_abs_le (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + (n : ℝ)| ≤ R := by
  classical
  obtain ⟨C, hC⟩ := exists_unit_of_sum_eq_zero E
  refine ⟨C + 1, fun t => ?_⟩

  have hmpos : 0 < ∑ w : InfinitePlace E, (mult w : ℝ) :=
    Finset.sum_pos (fun w _ => Nat.cast_pos.2 mult_pos) Finset.univ_nonempty
  set s : ℝ := (∑ w : InfinitePlace E, (mult w : ℝ) * t w) / ∑ w : InfinitePlace E, (mult w : ℝ) with hs
  have hms : (∑ w : InfinitePlace E, (mult w : ℝ)) * s = ∑ w : InfinitePlace E, (mult w : ℝ) * t w := by
    rw [hs]
    field_simp
  have hsum : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w - s) = 0 := by
    rw [Finset.sum_congr rfl fun w _ => mul_sub (mult w : ℝ) (t w) s, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hms, sub_self]
  obtain ⟨u, hu⟩ := hC (fun w => t w - s) hsum

  refine ⟨u, -⌊s⌋, fun w => ?_⟩
  have h1 := abs_le.1 (hu w)
  have h2 := Int.fract_nonneg s
  have h3 := Int.fract_lt_one s
  have hcoe : algebraMap (𝓞 E) E (u : 𝓞 E) = (u : E) := rfl
  have heq : t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + ((-⌊s⌋ : ℤ) : ℝ) =
      (t w - s + Real.log (w (u : E))) + Int.fract s := by
    rw [hcoe, Int.fract]
    push_cast
    ring
  rw [heq, abs_le]
  constructor <;> linarith [h1.1, h1.2]

end GlobalTheory.IntegerUnitBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterate
section
open scoped NNReal
open Finset

namespace GlobalTheory.DworkGhost


open scoped Classical in
open Classical in
noncomputable def coeff {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) : ℕ → A
  | n => if h : ((l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i))
      then h.choose else 0
decreasing_by exact i.isLt

theorem coeff_spec {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) (n : ℕ)
    (h : (l : A) ^ n ∣ φ^[n] a - ∑ i ∈ range n, (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  have h' : (l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i) := by
    rwa [Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]
  have e : coeff l φ a n = h'.choose := by
    rw [coeff, dite_eq_left h']
  have hc := h'.choose_spec
  rw [← e, Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n] at hc
  rw [sum_range_succ, Nat.sub_self, pow_zero, pow_one, ← hc]
  ring

theorem ghost_eq {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A)
    (hφ : ∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) (a : A) (n : ℕ) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  induction n with
  | zero => exact coeff_spec l φ a 0 (by simp)
  | succ n ih =>
    apply coeff_spec
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Function.iterate_succ_apply', ih, map_sum, ← sum_sub_distrib]
    apply dvd_sum
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [map_mul, map_pow, map_pow, map_natCast, ← mul_sub]
    have e1 : n + 1 = i + (n - i + 1) := by omega
    have e2 : n + 1 - i = n - i + 1 := by omega
    have e3 : coeff l φ a i ^ l ^ (n - i + 1) = (coeff l φ a i ^ l) ^ l ^ (n - i) := by
      rw [pow_succ', pow_mul]
    rw [e2, e3, e1, pow_add]
    exact mul_dvd_mul_left _ (dvd_sub_pow_of_dvd_sub (hφ (coeff l φ a i)) (n - i))

theorem exists_witt_ghost_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A,
      ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  intro l _ A _ φ hφ a
  refine ⟨WittVector.mk l (coeff l φ a), fun n => ?_⟩
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, ghost_eq l φ hφ a n]

end GlobalTheory.DworkGhost
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
section
open MeasureTheory

namespace GlobalTheory

theorem norm_mul_cexp_le_of_abs_le_on_support {s : ℂ} {f t : ℝ} {R : ℝ} (hf : 0 ≤ f) (hR : f ≠ 0 → |t| ≤ R) :
    ‖(f : ℂ) * Complex.exp (s * t)‖ ≤ f * Real.exp (‖s‖ * R) := by
  by_cases h0 : f = 0
  · simp [h0]
  have ht := hR h0
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  apply mul_le_mul_of_nonneg_left _ hf
  apply Real.exp_le_exp.mpr
  have h1 : (s * (t : ℂ)).re = s.re * t := by simp
  rw [h1]
  calc s.re * t ≤ |s.re * t| := le_abs_self _
    _ = |s.re| * |t| := abs_mul _ _
    _ ≤ ‖s‖ * R := mul_le_mul (Complex.abs_re_le_norm s) ht (abs_nonneg _) (norm_nonneg _)

theorem exp_integral_entire_real_pos {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ)
    (hfm : Measurable f) (htm : Measurable t) (hf0 : ∀ y, 0 ≤ f y)
    (hfi : Integrable f ν) (hR : ∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) :
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  obtain ⟨R, hR⟩ := hR
  have hmeas : ∀ s : ℂ, Measurable fun y => (f y : ℂ) * Complex.exp (s * t y) := by
    intro s; fun_prop
  have hint : ∀ s : ℂ, Integrable (fun y => (f y : ℂ) * Complex.exp (s * t y)) ν := by
    intro s
    refine Integrable.mono' (hfi.mul_const (Real.exp (‖s‖ * R))) (hmeas s).aestronglyMeasurable
      (ae_of_all _ fun y => norm_mul_cexp_le_of_abs_le_on_support (hf0 y) (hR y))
  refine ⟨?_, ?_⟩
  · intro s₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
      (F := fun s y => (f y : ℂ) * Complex.exp (s * t y))
      (F' := fun s y => (f y : ℂ) * (Complex.exp (s * t y) * t y))
      (bound := fun y => f y * R * Real.exp ((‖s₀‖ + 1) * R))
      (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable) (hint s₀)
      (by fun_prop : Measurable fun y => (f y : ℂ) * (Complex.exp (s₀ * t y) * t y)).aestronglyMeasurable
      (ae_of_all _ fun y s hs => ?_)
      ((hfi.mul_const R).mul_const _)
      (ae_of_all _ fun y s _ => ?_)
    · exact key.2.differentiableAt
    · by_cases h0 : f y = 0
      · simp [h0]
      have ht := hR y h0
      have hR0 : 0 ≤ R := (abs_nonneg _).trans ht
      have hs' : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' s s₀
        rw [Metric.mem_ball, dist_eq_norm] at hs
        linarith
      have e1 := norm_mul_cexp_le_of_abs_le_on_support (s := s) (hf0 y) (hR y)
      rw [← mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖(f y : ℂ) * Complex.exp (s * t y)‖ * |t y|
          ≤ (f y * Real.exp (‖s‖ * R)) * R := mul_le_mul e1 ht (abs_nonneg _) (mul_nonneg (hf0 y) (Real.exp_pos _).le)
        _ ≤ f y * R * Real.exp ((‖s₀‖ + 1) * R) := by
          have : Real.exp (‖s‖ * R) ≤ Real.exp ((‖s₀‖ + 1) * R) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs' hR0)
          have := mul_le_mul_of_nonneg_left this (mul_nonneg (hf0 y) hR0)
          nlinarith [this]
    · have := ((hasDerivAt_id s).mul_const (t y : ℂ)).cexp
      simp only [id, one_mul] at this
      exact this.const_mul (f y : ℂ)
  · intro r
    have hre : ∀ y, (f y : ℂ) * Complex.exp (r * t y) = ((f y * Real.exp (r * t y) : ℝ) : ℂ) := by
      intro y; push_cast; ring_nf
    simp_rw [hre]
    rw [integral_complex_ofReal]
    refine ⟨Complex.ofReal_im _, fun hpos => ?_⟩
    rw [Complex.ofReal_re]
    have gint : Integrable (fun y => f y * Real.exp (r * t y)) ν := by
      have := hint (r : ℂ)
      simp_rw [hre] at this
      exact this.re
    have hle : ∀ y, f y * Real.exp (-(|r| * R)) ≤ f y * Real.exp (r * t y) := by
      intro y
      by_cases h0 : f y = 0
      · simp [h0]
      apply mul_le_mul_of_nonneg_left _ (hf0 y)
      apply Real.exp_le_exp.mpr
      have ht := hR y h0
      have : |r * t y| ≤ |r| * R := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      linarith [neg_abs_le (r * t y)]
    calc 0 < (∫ y, f y ∂ν) * Real.exp (-(|r| * R)) := mul_pos hpos (Real.exp_pos _)
      _ = ∫ y, f y * Real.exp (-(|r| * R)) ∂ν := (integral_mul_const _ _).symm
      _ ≤ ∫ y, f y * Real.exp (r * t y) ∂ν := integral_mono (hfi.mul_const _) gint hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgInfSupOfIsCompl
section
open NumberField

namespace GlobalTheory

theorem fg_inf_sup_of_isCompl (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V) :
    A.FG → IsCompl U U' →
      (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  intro hA h
  let p : V →ₗ[K] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U U' h
  let q : V →ₗ[𝓞 K] V := p.restrictScalars (𝓞 K)
  have hpU : ∀ x, p x ∈ U := fun x => (Submodule.linearProjOfIsCompl U U' h x).2
  have hpl : ∀ x ∈ U, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left h ⟨x, hx⟩)
  have hpr : ∀ x ∈ U', p x = 0 := fun x hx => by
    have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff h).2 hx
    show ((Submodule.linearProjOfIsCompl U U' h x : U) : V) = 0
    exact congrArg Subtype.val this
  have hsub : ∀ x, x - p x ∈ U' := fun x => by
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff h]
    have h1 : p (x - p x) = 0 := by rw [map_sub, hpl _ (hpU x), sub_self]
    have h2 : ((Submodule.linearProjOfIsCompl U U' h (x - p x) : U) : V) = 0 := h1
    exact_mod_cast h2
  have heq : U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) = A.map q := by
    ext x
    constructor
    · rintro ⟨hxU, hx⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨a, ha, ?_⟩
      change p a = a + u
      have e1 : p (a + u) = a + u := hpl _ hxU
      rw [map_add (f := _), hpr u hu, add_zero] at e1
      exact e1
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hpU a, ?_⟩
      refine Submodule.mem_sup.2 ⟨a, ha, p a - a, ?_, by abel⟩
      have := U'.neg_mem (hsub a)
      simpa using this
  rw [heq]
  exact hA.map q

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltLaurentProdPreserves
section
open PowerSeries

namespace GlobalTheory

theorem filtLaurent_prod_preserves {L : Type} [Field L] (D : Module.End L L⟦X⟧) (e : ℕ → L)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - e i • f)
    (c : ℤ → L) (xs : List ℤ) (i : ℕ) (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ i ∣ Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction xs with
  | nil => simpa using hf
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]
    set g := Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f
    have h1 : X ^ i ∣ D g - e i • g := (pow_dvd_pow X (Nat.le_succ i)).trans (hD i g ih)
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c x) : Polynomial L) g
        = (D g - e i • g) + (e i - c x) • g := by
      simp [sub_smul, Module.algebraMap_end_apply]
    rw [h2]
    exact dvd_add h1 (Dvd.dvd.trans ih ⟨PowerSeries.C (e i - c x), by
      rw [PowerSeries.smul_eq_C_mul, mul_comm]⟩)

theorem filtLaurent_prod_raises {L : Type} [Field L] (D : Module.End L L⟦X⟧) (c : ℤ → L) (K : ℤ)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - c (-(K + i)) • f)
    (n : ℕ) : ∀ (xs : List ℤ) (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f →
      (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      X ^ (i + n) ∣ Polynomial.aeval D
        (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction n with
  | zero => exact fun xs i f hf _ => filtLaurent_prod_preserves D _ hD c xs i f hf
  | succ n ih =>
    intro xs i f hf hxs
    have hx : -(K + i) ∈ xs := hxs i le_rfl (by omega)
    have hperm := ((List.perm_cons_erase hx).map
      fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod_eq
    rw [hperm, List.map_cons, List.prod_cons, mul_comm, map_mul, Module.End.mul_apply]
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c (-(K + i))) : Polynomial L) f
        = D f - c (-(K + i)) • f := by
      simp [Module.algebraMap_end_apply]
    rw [h2, show i + (n + 1) = (i + 1) + n by omega]
    refine ih _ (i + 1) _ (hD i f hf) fun l hl hl' => ?_
    exact (List.mem_erase_of_ne (by omega)).2 (hxs l (by omega) (by omega))

noncomputable def filtLaurentDiag {L : Type} [Field L] (w : ℕ → L) : Module.End L L⟦X⟧ where
  toFun f := PowerSeries.mk fun i => w i * coeff i f
  map_add' f g := by ext i; simp [mul_add]
  map_smul' a f := by ext i; simp [mul_left_comm]

theorem filtLaurent_triangular {L : Type} [Field L] (w : ℕ → L) (p : L⟦X⟧)
    (hp : constantCoeff p ≠ 0) (i : ℕ) (a : L) (ha : constantCoeff p * a = w i)
    (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ (i + 1) ∣ (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f := by
  have h1 : (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f
      = p⁻¹ * (filtLaurentDiag w f - a • (p * f)) := by
    rw [mul_sub, mul_smul_comm, ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    rfl
  rw [h1]
  refine Dvd.dvd.mul_left ?_ _
  rw [X_pow_dvd_iff]
  intro l hl
  have hpf : X ^ i ∣ p * f := hf.mul_left p
  rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
  · simp [filtLaurentDiag, X_pow_dvd_iff.1 hf l h, X_pow_dvd_iff.1 hpf l h]
  · obtain ⟨g, rfl⟩ := hf
    have e1 : coeff l (X ^ l * g) = constantCoeff g := by
      simpa using coeff_X_pow_mul g l 0
    have e2 : coeff l (p * (X ^ l * g)) = constantCoeff p * constantCoeff g := by
      rw [mul_left_comm]
      simpa using coeff_X_pow_mul (p * g) l 0
    simp only [map_sub, filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, map_smul,
      e1, e2, smul_eq_mul, ← ha]
    ring

theorem filtLaurent_shift_line : ∀ (L : Type) [Field L] (M : Type) [AddCommGroup M] [Module L M] (Fl : ℤ → Submodule L M), Antitone Fl → ∀ (u : Lˣ) (p : PowerSeries L) (c : ℤ → L), PowerSeries.constantCoeff p ≠ 0 → (∀ x : ℤ, PowerSeries.constantCoeff p * c x = ((u ^ (-x) : Lˣ) : L) - 1) → ∀ (y' Y : ℕ) (xs : List ℤ), (∀ (a : ℤ) (j : ℕ), Fl (a + 1) ≠ Fl a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ℤ → M, (∀ m, ∃ k₀ : ℤ, ∀ k < k₀, seq m k = 0) → (∀ m < xs.length, ∀ k : ℤ, ∑ᶠ j : ℕ, PowerSeries.coeff j p • (seq (m + 1) (k - j) + c (xs.getD m 0) • seq m (k - j)) = (((u ^ k : Lˣ) : L) - 1) • seq m k) → (∀ k : ℤ, seq 0 k ∈ Fl (-k - Y)) → ∀ k : ℤ, seq xs.length k ∈ Fl (-k - y') := by
  intro L _ M _ _ Fl hFl u p c hp hc y' Y xs hxs seq hbd hrec h0 k
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  choose k₀ hk₀ using hbd

  have core : ∀ (K : ℤ), (∀ m ≤ xs.length, K ≤ k₀ m) → ∀ i n : ℕ,
      (∀ l < i, φ (seq 0 (K + l)) = 0) → (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      ∀ l < i + n, φ (seq xs.length (K + l)) = 0 := by
    intro K hK i n hi hn
    set w : ℕ → L := fun l => ((u ^ (K + l) : Lˣ) : L) - 1 with hw
    set D : Module.End L L⟦X⟧ := LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w with hDdef
    set G : ℕ → L⟦X⟧ := fun m => PowerSeries.mk fun l => φ (seq m (K + l)) with hG
    have hstep : ∀ m < xs.length, G (m + 1) = D (G m) - c (xs.getD m 0) • G m := by
      intro m hm
      have key : p * (G (m + 1) + c (xs.getD m 0) • G m) = filtLaurentDiag w (G m) := by
        ext l
        have h1 := hrec m hm (K + l)
        rw [finsum_eq_sum_of_support_subset (s := Finset.range (l + 1))] at h1
        · have h2 := congrArg φ h1
          rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => coeff a p * coeff b (G (m + 1) + c (xs.getD m 0) • G m))]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, map_smul] at h2
          simp only [filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, hG, hw]
          rw [← smul_eq_mul, ← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : j ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have : K + ((l - j : ℕ) : ℤ) = K + l - j := by omega
          simp only [map_add (f := _), map_smul, coeff_mk, this, smul_eq_mul]
        · intro j hj
          by_contra hj'
          have hj'' : l + 1 ≤ j := by simpa using hj'
          have a1 := hK m hm.le
          have a2 := hK (m + 1) hm
          apply hj
          simp only
          rw [hk₀ (m + 1) _ (by omega), hk₀ m _ (by omega)]
          simp
      rw [eq_sub_iff_add_eq, hDdef, LinearMap.comp_apply, ← key, LinearMap.mulLeft_apply,
        ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    have hall : ∀ m ≤ xs.length, G m = Polynomial.aeval D
        ((xs.take m).map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod
          (G 0) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro hm
        have hm' : m < xs.length := hm
        rw [hstep m hm', List.take_succ_eq_append_getElem hm', List.map_append, List.prod_append,
          mul_comm, map_mul, Module.End.mul_apply, ← ih hm'.le, List.getD_eq_getElem _ _ hm']
        simp [Module.algebraMap_end_apply]
    have hfin := filtLaurent_prod_raises D c K (fun l f hf =>
      filtLaurent_triangular w p hp l _ (by rw [hc, neg_neg]) f hf) n xs i (G 0)
      (X_pow_dvd_iff.2 fun l hl => by simpa [hG] using hi l hl) hn
    have h3 := hall xs.length le_rfl
    rw [List.take_length] at h3
    rw [← h3] at hfin
    intro l hl
    simpa [hG] using X_pow_dvd_iff.1 hfin l hl
  obtain ⟨K₀, hK₀⟩ := ((Set.finite_le_nat xs.length).image k₀).bddBelow
  have hK₁ : ∀ m ≤ xs.length, K₀ ≤ k₀ m := fun m hm => hK₀ ⟨m, hm, rfl⟩
  by_cases hex : ∃ a : ℤ, ¬ ∀ v ∈ Fl a, φ v = 0
  · have hbdd : ∀ a : ℤ, (¬ ∀ v ∈ Fl a, φ v = 0) → a < -k - y' := by
      intro a ha
      by_contra h
      exact ha fun v hv => hφ v (hFl (not_lt.1 h) hv)
    obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd
      ⟨-k - y', fun a ha => (hbdd a ha).le⟩ hex
    have ha1 : ∀ v ∈ Fl (a + 1), φ v = 0 := by
      by_contra h
      have := hmax _ h
      omega
    have hjump : Fl (a + 1) ≠ Fl a := fun h => ha (h ▸ ha1)
    have hlt := hbdd a ha
    set K := min K₀ (min k (-a - Y)) with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) (-a - Y - K).toNat (Y - y')
      (fun l hl => ha1 _ (hFl (by omega) (h0 _)))
      (fun l hl hl' => by
        have := hxs a (-(K + l) - a).toNat hjump (by omega) (by omega)
        convert this using 1
        omega) (k - K).toNat (by omega)
    convert this using 3
    omega
  · push Not at hex
    set K := min K₀ k with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) ((k - K).toNat + 1) 0
      (fun l _ => hex _ _ (h0 _)) (fun l hl hl' => by omega) (k - K).toNat (by omega)
    convert this using 3
    omega

end GlobalTheory
end

