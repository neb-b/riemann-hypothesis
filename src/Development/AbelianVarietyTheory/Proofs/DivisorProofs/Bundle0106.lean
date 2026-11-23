module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralSuperposition
section
open MeasureTheory

namespace GlobalTheory
namespace SchwartzIntegralExchange

theorem exists_factor {S X : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (J : S →ₗ[ℂ] X) (Λ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖Λ w‖ ≤ C * ‖J w‖) :
    ∃ g : X →L[ℂ] ℂ, ∀ w, g (J w) = Λ w := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective J.rangeRestrict
    J.range_rangeRestrict
  have hr' : ∀ y : LinearMap.range J, J (r y) = y := fun y => by
    have := congrArg (fun φ : LinearMap.range J →ₗ[ℂ] LinearMap.range J => (φ y : X)) hr
    simpa using this
  let f : LinearMap.range J →L[ℂ] ℂ := (Λ ∘ₗ r).mkContinuous C (fun y => by
    have := h (r y)
    rw [hr'] at this
    simpa using this)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨g, fun w => ?_⟩
  have h1 := hg ⟨J w, w, rfl⟩
  have h2 := h (r ⟨J w, w, rfl⟩ - w)
  rw [map_sub J, hr'] at h2
  simp only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, map_sub, sub_eq_zero] at h2
  rw [← h2]
  simpa [f] using h1

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x)
    ((continuous_norm.pow k).smul ((w.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k n w)
    (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact SchwartzMap.le_seminorm ℂ k n w x)

theorem wtFun_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wtFun k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl

theorem norm_wtFun_le (k n : ℕ) (w : SchwartzMap E ℂ) :
    ‖wtFun k n w‖ ≤ SchwartzMap.seminorm ℂ k n w :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _

theorem le_norm_wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℂ k n w ≤ ‖wtFun k n w‖ := by
  refine SchwartzMap.seminorm_le_bound ℂ k n w (norm_nonneg _) (fun x => ?_)
  have := (wtFun k n w).norm_coe_le_norm x
  rwa [wtFun_apply, norm_smul, Real.norm_of_nonneg (by positivity)] at this

noncomputable def wt (k n : ℕ) : SchwartzMap E ℂ →L[ℂ]
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (wtFun k n)
    (fun f g => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      have hg : ContDiffAt ℝ n g x := ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.add_apply, wtFun_apply, wtFun_apply, wtFun_apply, ← smul_add,
        ← iteratedFDeriv_add_apply hf hg]
      rfl)
    (fun a f => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.smul_apply, wtFun_apply, wtFun_apply, RingHom.id_apply,
        smul_comm a, ← iteratedFDeriv_const_smul_apply hf]
      rfl)
    ⟨{(k, n)}, 1, zero_le_one, fun f => by
      simpa using norm_wtFun_le k n f⟩

theorem wt_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wt k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl

theorem continuous_iteratedFDeriv_at (n : ℕ) (x : E) :
    Continuous (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) := by
  have : (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) = fun w => wt 0 n w x := by
    funext w; simp [wt_apply]
  rw [this]
  exact (continuous_eval_const x).comp (wt 0 n).continuous

variable {P : Type} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {ν : Measure P} {Φ : P → SchwartzMap E ℂ} {c : P → ℂ}

theorem integrable_iteratedFDeriv (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (n : ℕ) (x : E) : Integrable (fun ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x) ν := by
  refine (hi 0 n).mono' (hc.smul
    ((continuous_iteratedFDeriv_at n x).comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ n x)
    (norm_nonneg _)

theorem iteratedFDeriv_integral (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (u : E → ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (n : ℕ) :
    ∀ x, iteratedFDeriv ℝ n u x = ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν := by
  induction n with
  | zero =>
    intro x
    ext m
    rw [ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv hΦ hc hi 0 x)]
    simp [hu]
  | succ n ih =>
    intro x
    set L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ with hL
    have hfun : iteratedFDeriv ℝ n u = fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν :=
      funext ih
    have hd : HasFDerivAt (fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν)
        (∫ ξ, L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x) ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
        (F := fun x ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x)
        (F' := fun x ξ => L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x))
        (bound := fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ 0 (n + 1) (Φ ξ))
        Filter.univ_mem
        (Filter.Eventually.of_forall fun y =>
          (integrable_iteratedFDeriv hΦ hc hi n y).aestronglyMeasurable)
        (integrable_iteratedFDeriv hΦ hc hi n x)
        (L.continuous.comp_aestronglyMeasurable
          (integrable_iteratedFDeriv hΦ hc hi (n + 1) x).aestronglyMeasurable)
        (ae_of_all _ fun ξ y _ => ?_) (hi 0 (n + 1)) (ae_of_all _ fun ξ y _ => ?_)
      · rw [LinearIsometryEquiv.norm_map, norm_smul]
        exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ _ y)
          (norm_nonneg _)
      · have h1 : DifferentiableAt ℝ (iteratedFDeriv ℝ n (Φ ξ)) y :=
          ((Φ ξ).smooth ⊤).differentiable_iteratedFDeriv
            (by exact_mod_cast ENat.coe_lt_top n) y
        have h2 := h1.hasFDerivAt.const_smul (c ξ)
        rw [fderiv_iteratedFDeriv] at h2
        exact h2
    have h3 := hd.fderiv
    rw [← hfun, fderiv_iteratedFDeriv] at h3
    apply L.injective
    exact h3.trans (L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (integrable_iteratedFDeriv hΦ hc hi (n + 1) x))

theorem integrable_wt (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (k n : ℕ) : Integrable (fun ξ => c ξ • wt k n (Φ ξ)) ν := by
  refine (hi k n).mono' (hc.smul
    ((wt k n).continuous.comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_wtFun_le k n _) (norm_nonneg _)

theorem wt_integral (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (u : SchwartzMap E ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (k n : ℕ) :
    wt k n u = ∫ ξ, c ξ • wt k n (Φ ξ) ∂ν := by
  ext1 x
  have := (BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm
    (integrable_wt hΦ hc hi k n)
  simp only [BoundedContinuousFunction.evalCLM_apply] at this
  rw [← this, wt_apply, iteratedFDeriv_integral hΦ hc hi u hu n x, ← integral_smul]
  congr 1
  funext ξ
  rw [BoundedContinuousFunction.smul_apply, wt_apply, smul_comm]

end SchwartzIntegralExchange


open SchwartzIntegralExchange in
theorem schwartz_clm_integral_comm :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by
  intro E _ _ P _ _ _ _ ν Φ hΦ c hc hi u hu Λ
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp Λ.toLinearMap) (continuous_norm.comp Λ.continuous)
  let J : SchwartzMap E ℂ →L[ℂ] (∀ i : s, BoundedContinuousFunction E
      (ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)) :=
    ContinuousLinearMap.pi fun i => wt i.1.1 i.1.2
  obtain ⟨g, hg⟩ := exists_factor J.toLinearMap Λ.toLinearMap C (fun w => by
    have h1 : ‖Λ w‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) w := hC w
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    exact (le_norm_wtFun i.1 i.2 w).trans (norm_le_pi_norm (J w) ⟨i, hi⟩))
  have hg' : ∀ w, g (J w) = Λ w := hg
  have hint : Integrable (fun ξ => c ξ • J (Φ ξ)) ν :=
    integrable_pi_iff.2 fun i => integrable_wt hΦ hc hi i.1.1 i.1.2
  have hJ : J u = ∫ ξ, c ξ • J (Φ ξ) ∂ν := by
    funext i
    rw [eval_integral (integrable_pi_iff.1 hint)]
    exact wt_integral hΦ hc hi u hu i.1.1 i.1.2
  rw [← hg', hJ, ← g.integral_comp_comm hint]
  simp [hg']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPairingContinuousFunctional
section
open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_pairing_conj_clm_of_borelSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ) :
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by
  let kc : 𝓢(V, ℂ) := SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) k
  have hkc : ∀ x, kc x = starRingEnd ℂ (k x) := fun x => rfl
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (k x)) := by
    have := kc.hasTemperateGrowth
    simpa [funext hkc] using this
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp
    (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (k x))), fun u => ?_⟩
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply hg]
  congr 1
  funext x
  simp [smul_eq_mul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
section
open scoped SchwartzMap
open Complex

namespace GlobalTheory.LinPhaseSeminorm

theorem iteratedDeriv_const_mul_cexp (a c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => c * Complex.exp (a * y)) =
      fun y : ℝ => c * a ^ n * Complex.exp (a * y) := by
  induction n generalizing c with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => c * Complex.exp (a * y)) =
        fun y : ℝ => (c * a) * Complex.exp (a * y) := by
      funext y
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      have h : HasDerivAt (fun y : ℝ => c * Complex.exp (a * y))
          (c * (Complex.exp (a * y) * (a * 1))) y :=
        ((h1.const_mul a).cexp).const_mul c
      rw [h.deriv]; ring
    rw [hd, ih]; funext y; ring

theorem norm_cexp_neg_two_pi_I_mul (r : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

noncomputable def phaseLine (c t : ℝ) : ℝ → ℂ := fun y =>
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
    Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ))

theorem phase_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c t : ℝ) :
    (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = phaseLine c t ∘ ⇑L := by
  funext x
  simp only [phaseLine, Function.comp_apply, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem contDiff_phaseLine (c t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phaseLine c t) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold phaseLine; fun_prop

theorem norm_iteratedDeriv_phaseLine (c t : ℝ) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (phaseLine c t) y‖ = (2 * Real.pi * |t|) ^ i := by
  have e : phaseLine c t = fun y : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
        Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)) := rfl
  rw [e, iteratedDeriv_const_mul_cexp]
  have h2 : (-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)
      = -(2 * Real.pi * Complex.I) * ((t * y : ℝ) : ℂ) := by push_cast; ring
  simp only
  rw [h2, norm_mul, norm_mul, norm_cexp_neg_two_pi_I_mul, norm_cexp_neg_two_pi_I_mul, norm_pow]
  simp [abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_phase_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c : ℝ) {t : ℝ} (ht : |t| ≤ 1) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ ≤ (2 * Real.pi * ‖L‖) ^ i := by
  rw [L.iteratedFDeriv_comp_right (contDiff_phaseLine c t) x (i := i) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i (phaseLine c t) (L x)‖ * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (2 * Real.pi * |t|) ^ i * ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_phaseLine]; simp
    _ ≤ (2 * Real.pi * 1) ^ i * ‖L‖ ^ i := by gcongr
    _ = (2 * Real.pi * ‖L‖) ^ i := by ring

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c t : ℝ) : Function.HasTemperateGrowth (phaseLine c t ∘ ⇑L) := by
  refine ⟨(contDiff_phaseLine c t).comp L.contDiff, fun n => ⟨0, (2 * Real.pi * |t| * ‖L‖) ^ n, fun x => ?_⟩⟩
  rw [L.iteratedFDeriv_comp_right (contDiff_phaseLine c t) x (i := n) (by exact_mod_cast le_top),
    pow_zero, mul_one]
  calc _ ≤ ‖iteratedFDeriv ℝ n (phaseLine c t) (L x)‖ * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (2 * Real.pi * |t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_phaseLine]; simp [mul_pow]

theorem seminorm_smulLeft_phase_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c : ℝ) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → ∀ f : 𝓢(V, ℂ),
      SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ
        (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f)
        ≤ C * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f := by
  intro V _ _ L c k n
  set B : ℝ := 2 ^ n * (1 + 2 * Real.pi * ‖L‖) ^ n with hB
  refine ⟨(n + 1) * B, fun t ht f => ?_⟩
  rw [phase_eq L c t]
  set S := ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => apply_nonneg _ _
  have hL0 : 0 ≤ 2 * Real.pi * ‖L‖ := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have happ : (⇑(SchwartzMap.smulLeftCLM ℂ (phaseLine c t ∘ ⇑L) f))
      = fun y => (phaseLine c t ∘ ⇑L) y * f y := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L c t), smul_eq_mul]
  rw [happ]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_phaseLine c t).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ B * S := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_phase_le L c ht i x
    have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ S :=
      (SchwartzMap.le_seminorm ℂ k (n - i) f x).trans
        (Finset.single_le_sum (f := fun m => SchwartzMap.seminorm ℂ k m f)
          (fun m _ => apply_nonneg _ _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n i))))
    have hc : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
    have h4 : (2 * Real.pi * ‖L‖) ^ i ≤ (1 + 2 * Real.pi * ‖L‖) ^ n :=
      calc (2 * Real.pi * ‖L‖) ^ i ≤ (1 + 2 * Real.pi * ‖L‖) ^ i := by gcongr; linarith
        _ ≤ (1 + 2 * Real.pi * ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi'
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        = ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ (2 ^ n * (1 + 2 * Real.pi * ‖L‖) ^ n) * S := by
          gcongr
          exact h1.trans h4
      _ = B * S := by rw [hB]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (phaseLine c t ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), B * S := Finset.sum_le_sum hterm
    _ = (n + 1) * B * S := by simp; ring

end GlobalTheory.LinPhaseSeminorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzShiftIteratedFDerivBound
section
open scoped ContDiff

namespace GlobalTheory

theorem schwartz_shift_iteratedFDeriv_bound
    {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  set S : ℝ := 2 ^ M * (Finset.Iic (M, n)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hS
  set B : ℝ := ‖a‖ + ‖p‖ * max R 0 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨‖p‖ ^ n * ((1 + B) ^ M * S), fun y t ht => ?_⟩
  have hy0 : 0 < (1 + ‖y‖) ^ M := by positivity

  have hcomp : (fun t => f (y + a + p t)) = (fun v => f (y + a + v)) ∘ p := rfl
  have hg : ContDiff ℝ ∞ (fun v => f (y + a + v)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  have e1 := ContinuousLinearMap.iteratedFDeriv_comp_right p hg t (i := n)
    (by exact_mod_cast le_top)
  have e2 : iteratedFDeriv ℝ n (fun v => f (y + a + v)) (p t)
      = iteratedFDeriv ℝ n f (y + a + p t) := iteratedFDeriv_comp_add_left n (y + a) (p t)
  set v := y + a + p t with hv
  have hD : ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := by
    rw [hcomp, e1, e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const, mul_comm]

  have hdec : (1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, n)) le_rfl le_rfl f v

  have hpt : ‖p t‖ ≤ ‖p‖ * max R 0 :=
    (p.le_opNorm t).trans (mul_le_mul_of_nonneg_left (ht.trans (le_max_left _ _)) (norm_nonneg _))
  have hyv : 1 + ‖y‖ ≤ (1 + ‖v‖) * (1 + B) := by
    have : y = v - a - p t := by rw [hv]; abel
    have h1 : ‖y‖ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by
      rw [this]
      calc ‖v - a - p t‖ ≤ ‖v - a‖ + ‖p t‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by gcongr; exact norm_sub_le _ _
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith [mul_nonneg hv0 hB0]
  have hyM : (1 + ‖y‖) ^ M ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hyv M
  have hDf0 : 0 ≤ ‖iteratedFDeriv ℝ n f v‖ := norm_nonneg _
  have key : (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S := by
    calc (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖
        ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M * ‖iteratedFDeriv ℝ n f v‖ :=
          mul_le_mul_of_nonneg_right hyM hDf0
      _ = (1 + B) ^ M * ((1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖) := by ring
      _ ≤ (1 + B) ^ M * S := mul_le_mul_of_nonneg_left hdec (by positivity)
  have hf' : ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hy0, mul_comm]; exact key
  calc ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := hD
    _ ≤ ‖p‖ ^ n * ((1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹) :=
        mul_le_mul_of_nonneg_left hf' (by positivity)
    _ = ‖p‖ ^ n * ((1 + B) ^ M * S) * ((1 + ‖y‖) ^ M)⁻¹ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzWeightedSobolevOfFinrankZero
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_weighted_sobolev_of_finrank_zero :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ hE k n
  haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
  have hcpt : IsCompact (univ : Set E) := (Set.subsingleton_univ).isCompact
  have hfin : μ univ ≠ ∞ := hcpt.measure_lt_top.ne
  have hne : μ univ ≠ 0 := isOpen_univ.measure_ne_zero μ univ_nonempty
  set m : ℝ := μ.real univ with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hne hfin
  refine ⟨n, Real.sqrt m⁻¹, Real.sqrt_nonneg _, fun f x => ?_⟩
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  set a : ℝ := ‖iteratedFDeriv ℝ n f (0 : E)‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have h1 : ‖(0 : E)‖ ^ k * a ≤ a := by
    apply mul_le_of_le_one_left ha0
    rw [norm_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  refine h1.trans ?_
  have hterm : ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2 ∂μ = m * a ^ 2 := by
    have : (fun z : E => (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2) = fun _ => a ^ 2 := by
      funext z
      rw [Subsingleton.elim z 0, pow_zero, one_mul]
    rw [this, integral_const, smul_eq_mul]
  have hnn : ∀ i j : ℕ, 0 ≤ ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ :=
    fun i j => integral_nonneg fun z => sq_nonneg _
  have hle : m * a ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ := by
    rw [← hterm]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ∑ j ∈ Finset.range (n + 1),
        ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
      (Finset.mem_range.mpr (Nat.succ_pos n)))
    exact Finset.single_le_sum
      (f := fun j => ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun j _ => hnn 0 j) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rw [← Real.sqrt_mul (inv_nonneg.mpr hmpos.le)]
  apply Real.le_sqrt_of_sq_le
  calc a ^ 2 = m⁻¹ * (m * a ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hmpos.le)

end GlobalTheory
end

