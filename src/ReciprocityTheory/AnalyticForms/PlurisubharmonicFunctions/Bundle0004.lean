module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenPolar
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ComplexHessianIsHermitianOfContDiffAt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshLap
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LeviOneEqLaplacianThm
section
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian

namespace ReciprocityTheory.AnForm.A

open GreenFunction

noncomputable section

theorem exists_R_of_compact {F : Type} [NormedAddCommGroup F] {u : F → ℝ}
    (hc : HasCompactSupport u) : ∃ R > 0, ∀ q, q ∈ tsupport u → ‖q‖ ≤ R := by
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : F)).1 hc.isCompact.isBounded
  refine ⟨max R0 0 + 1, by positivity, fun q hq => ?_⟩
  have := hR0 hq
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R0 0]

theorem leviOne (u : ℂ → ℝ) (z : ℂ) :
    ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) (Pi.single 0 1) =
      Δ u z / 4 := by
  set e0 : (Fin 1 → ℂ) ≃L[ℝ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ with he0
  set Φ : (ℂ →L[ℝ] ℝ) ≃L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) :=
    e0.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with hΦ
  have h1 : (fun w : Fin 1 → ℂ => u (w 0)) = u ∘ e0 := rfl
  have h2 : fderiv ℝ (u ∘ e0) = Φ ∘ (fderiv ℝ u ∘ e0) := by
    funext w
    rw [e0.comp_right_fderiv]
    ext v
    simp [Φ]
  have h3 : ∀ x, fderiv ℝ (Φ ∘ (fderiv ℝ u ∘ e0)) x =
      (Φ : (ℂ →L[ℝ] ℝ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ)).comp
        ((fderiv ℝ (fderiv ℝ u) (e0 x)).comp (e0 : (Fin 1 → ℂ) →L[ℝ] ℂ)) := fun x => by
    rw [Φ.comp_fderiv, e0.comp_right_fderiv]
  simp only [ReciprocityTheory.AnForm.levi, h1, h2, h3, laplacian_eq_fderiv_fderiv]
  simp [Φ, e0]

theorem greenParamFiber_main : GreenParamFiberStatement := by
  intro E _ _ _ u hu hc p
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hv : ContDiff ℝ 2 (fun w : ℂ => u (w, p)) := hu.comp (contDiff_id.prodMk contDiff_const)
  have h := green_at hv 0 (R := R + 1) (by linarith) (fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR _ hm
      have := norm_fst_le (z, p)
      simp only [sub_zero] at hz
      linarith)
  simpa using h

theorem lap_fiber {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℂ × E → ℝ}
    (hu : ContDiff ℝ 2 u) (z : ℂ) (p : E) :
    Δ (fun w : ℂ => u (w, p)) z = fderiv ℝ (fderiv ℝ u) (z, p) (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ u) (z, p) (Complex.I, 0) (Complex.I, 0) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set L : ℂ →L[ℝ] ℂ × E := (ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] E) with hL
  set Ψ : ((ℂ × E) →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ ℂ (ℂ × E) ℝ).flip L with hΨ
  have hpath : ∀ w : ℂ, HasFDerivAt (fun w : ℂ => (w, p)) L w := fun w =>
    (hasFDerivAt_id w).prodMk (hasFDerivAt_const p w)
  have h1 : fderiv ℝ (fun w : ℂ => u (w, p)) = fun w => Ψ (fderiv ℝ u (w, p)) := by
    funext w
    exact ((hd _).hasFDerivAt.comp w (hpath w)).fderiv
  have h2 : HasFDerivAt (fun w : ℂ => Ψ (fderiv ℝ u (w, p)))
      (Ψ.comp ((fderiv ℝ (fderiv ℝ u) (z, p)).comp L)) z :=
    Ψ.hasFDerivAt.comp z ((hd2 _).hasFDerivAt.comp z (hpath z))
  rw [laplacian_eq_fderiv_fderiv, h1, h2.fderiv]
  simp [Ψ, L]

theorem greenParam_main : GreenParamStatement := by
  intro E _ _ _ _ _ μ _ u hu hc
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  set G : ℂ × E → ℝ := fun q => fderiv ℝ (fderiv ℝ u) q (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ u) q (Complex.I, 0) (Complex.I, 0) with hG
  have hGc : Continuous G := by fun_prop
  have hF : (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1) =
      fun q => Real.log ‖q.1‖ * G q := by
    funext q; rw [lap_fiber hu]
  have hG0 : ∀ q, q ∉ tsupport u → G q = 0 := fun q hq => by
    have : fderiv ℝ (fderiv ℝ u) q = 0 := by
      by_contra h
      exact hq (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ
        (subset_tsupport (fderiv ℝ (fderiv ℝ u)) h)))
    simp [G, this]
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn hGc.continuousOn
  have hint : Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
      ((volume : Measure ℂ).prod μ) := by
    rw [hF]
    have hg1 : Integrable (fun z : ℂ => max C 0 * (Iic R).indicator (fun t => ‖Real.log t‖) ‖z‖) :=
      (integrable_log_norm_ball hR0).const_mul _
    have hg2 : Integrable (fun p : E => (Metric.closedBall (0 : E) R).indicator (fun _ => (1 : ℝ)) p) μ :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
        (integrableOn_const (isCompact_closedBall 0 R).measure_lt_top.ne)
    refine (hg1.mul_prod hg2).mono'
      ((Real.measurable_log.comp (measurable_norm.comp measurable_fst)).aestronglyMeasurable.mul
        hGc.aestronglyMeasurable) (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ tsupport u
    · have hn := hR q hq
      have h1 : ‖q.1‖ ∈ Iic R := by simp only [mem_Iic]; linarith [norm_fst_le q]
      have h2 : q.2 ∈ Metric.closedBall (0 : E) R := by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [norm_snd_le q]
      simp only [indicator_of_mem h1, indicator_of_mem h2, mul_one, norm_mul]
      rw [mul_comm (max C 0)]
      exact mul_le_mul_of_nonneg_left ((hC q hq).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hG0 q hq, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (le_max_right _ _)
        (indicator_nonneg (fun _ _ => norm_nonneg _) _))
        (indicator_nonneg (fun _ _ => zero_le_one) _)
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  simp only
  rw [integral_congr_ae (Eventually.of_forall fun p => (greenParamFiber_main E u hu hc p).2)]
  exact integral_const_mul _ _

theorem greenParam_thm : GreenParamStatement := greenParam_main

end

end ReciprocityTheory.AnForm.A
end

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Matrix

noncomputable section

variable {D E : ℕ}

def jacC (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) : Matrix (Fin E) (Fin D) ℂ :=
  Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a

theorem jacC_eq_toMatrix' (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) :
    jacC τ z = LinearMap.toMatrix' (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin E → ℂ)) := by
  ext a k
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem det_jacC (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ) :
    (jacC τ z).det = LinearMap.det (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) := by
  rw [jacC_eq_toMatrix', LinearMap.det_toMatrix']

theorem hessC_isHermitian (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  exact TraceConjugationCover.complexHessian_isHermitian_of_contDiffAt φ z hφ

theorem hessC_add (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  exact TraceConjugationCover.complexHessian_add_of_contDiffAt φ ψ z hφ hψ

theorem hessC_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    hessC (φ ∘ τ) z = (jacC τ z)ᵀ * hessC φ (τ z) * (jacC τ z).map (starRingEnd ℂ) := by
  exact TraceConjugationCover.complexHessian_comp_holomorphic_matrix φ τ z hτ hφ

theorem maDens_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z)) :
    maDens (fun k => φ k ∘ τ) z = maDens φ (τ z) * Complex.normSq (jacC τ z).det := by
  have h : (fun k => hessC (φ k ∘ τ) z) =
      fun k => (jacC τ z)ᵀ * hessC (φ k) (τ z) * (jacC τ z).map (starRingEnd ℂ) :=
    funext fun k => hessC_comp (φ k) τ z hτ (hφ k)
  simp only [maDens]
  rw [h, mdisc_transpose_mul_mul_conj, Complex.re_ofReal_mul]
  ring

theorem hessC_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  exact hessC_log_norm' g z hg hz

theorem hessC_add_log_norm (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  exact hessC_add_log_norm' φ g z hφ hg hz

theorem hessC_add_re_analytic (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  exact hessC_add_re_analytic' φ G z hφ hG

theorem det_restrictScalars_real {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

theorem det_fderiv_real_eq_normSq (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ)
    (hτ : DifferentiableAt ℂ τ z) :
    (fderiv ℝ τ z).det = Complex.normSq (jacC τ z).det := by
  rw [(hτ.hasFDerivAt.restrictScalars ℝ).fderiv, det_jacC]
  exact det_restrictScalars_real (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

theorem integral_image_eq_integral_normSq_det_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    ∫ w in τ '' U, f w = ∫ z in U, Complex.normSq (jacC τ z).det • f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem lintegral_image_eq_lintegral_normSq_det_mul (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (U : Set (Fin D → ℂ)) (hU : IsOpen U) (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U)
    (f : (Fin D → ℂ) → ENNReal) :
    ∫⁻ w in τ '' U, f w = ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (jacC τ z).det) * f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem integrableOn_image_iff_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    IntegrableOn f (τ '' U) ↔
      IntegrableOn (fun z => Complex.normSq (jacC τ z).det • f (τ z)) U := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem hessC_sum_normSq (z : Fin D → ℂ) :
    hessC (fun w => ∑ i, Complex.normSq (w i)) z = 1 := by
  exact TraceConjugationCover.complexHessian_sum_normSq_coord z

end

end ReciprocityTheory.AnForm.A
end

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
section
open MeasureTheory Metric Set Filter Topology Real

namespace ReciprocityTheory.AnForm.A.PshLap

noncomputable section

variable {D : ℕ}

def L0 (w : Fin D → ℂ) : ℂ →L[ℝ] (Fin D → ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight w

def Pc (w : Fin D → ℂ) : ((Fin D → ℂ) →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ ℂ (Fin D → ℂ) ℝ).flip (L0 w)

def Gc (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℝ :=
  Pc w (fderiv ℝ φ (z + ζ • w))

def Hc (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (Pc w).comp ((fderiv ℝ (fderiv ℝ φ) (z + ζ • w)).comp (L0 w))

lemma complexLine_apply (w : Fin D → ℂ) (a : ℂ) : L0 w a = a • w := by simp [L0]

lemma Pc_apply (w : Fin D → ℂ) (T : (Fin D → ℂ) →L[ℝ] ℝ) (a : ℂ) : Pc w T a = T (a • w) := by
  simp [Pc, L0]

lemma Hc_apply (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ a b : ℂ) :
    Hc φ z w ζ a b = fderiv ℝ (fderiv ℝ φ) (z + ζ • w) (a • w) (b • w) := by
  simp [Hc, Pc, L0]

lemma hasFDerivAt_line (z w : Fin D → ℂ) (ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => z + ζ • w) (L0 w) ζ :=
  ((hasFDerivAt_id ζ).smul_const w).const_add z

variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

lemma line_hasFDerivAt_g (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) {ζ : ℂ}
    (hζ : z + ζ • w ∈ U) : HasFDerivAt (fun ζ : ℂ => φ (z + ζ • w)) (Gc φ z w ζ) ζ := by
  have hd : HasFDerivAt φ (fderiv ℝ φ (z + ζ • w)) (z + ζ • w) :=
    ((hφ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hζ)).hasFDerivAt
  refine (hd.comp ζ (hasFDerivAt_line z w ζ)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun a => ?_
  simp [Gc, Pc_apply, complexLine_apply]

lemma line_hasFDerivAt_G (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) {ζ : ℂ}
    (hζ : z + ζ • w ∈ U) : HasFDerivAt (Gc φ z w) (Hc φ z w ζ) ζ := by
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z + ζ • w)) (z + ζ • w) :=
    ((h2.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hζ)).hasFDerivAt
  exact (Pc w).hasFDerivAt.comp ζ (hd.comp ζ (hasFDerivAt_line z w ζ))

lemma line_contOn_H (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) :
    ContinuousOn (Hc φ z w) {ζ : ℂ | z + ζ • w ∈ U} := by
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h3 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U := h2.continuousOn_fderiv_of_isOpen hU le_rfl
  have hl : Continuous (fun ζ : ℂ => z + ζ • w) := by fun_prop
  exact continuousOn_const.clm_comp
    ((h3.comp hl.continuousOn (fun ζ h => h)).clm_comp continuousOn_const)

lemma circ_smul (r θ : ℝ) (w : Fin D → ℂ) :
    circleMap 0 r θ • w = circleMap 0 1 θ • ((r:ℂ) • w) := by
  ext i
  simp [circleMap]
  ring

theorem plurisubharmonicIffLeviNonneg_holds : IsPsh_iff_isLeviPshStatement := by
  intro D U φ hU hφ
  constructor
  · rintro ⟨-, hsub⟩
    refine ⟨hφ, fun z hz w => ?_⟩
    set V := {ζ : ℂ | z + ζ • w ∈ U} with hV
    have hVo : IsOpen V := hU.preimage (by fun_prop)
    have h0 : (0:ℂ) ∈ V := by simpa [V] using hz
    obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.mp hVo 0 h0
    have hR' : closedBall (0:ℂ) (R/2) ⊆ V := (closedBall_subset_ball (by linarith)).trans hR
    have key := lap_nonneg_of_sub_mean (V := V) (g := fun ζ => φ (z + ζ • w)) (G := Gc φ z w)
      (H := Hc φ z w) (fun ζ hζ => line_hasFDerivAt_g hU hφ z w hζ)
      (fun ζ hζ => line_hasFDerivAt_G hU hφ z w hζ) (line_contOn_H hU hφ z w)
      (by linarith : (0:ℝ) < R/2) hR' ?_
    · rw [Hc_apply, Hc_apply] at key
      simp only [zero_smul, add_zero, one_smul] at key
      unfold levi
      linarith
    · intro r hr
      have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • ((r:ℂ) • w) ∈ U := by
        intro ζ hζ
        rw [smul_smul]
        apply hR'
        rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr.1]
        nlinarith [norm_nonneg ζ, hr.2]
      have h1 := (hsub z ((r:ℂ) • w) hmem).2
      simp only [zero_smul, add_zero]
      convert h1 using 1
      rw [Real.circleAverage_def, Real.circleAverage_def]
      congr 1
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [circ_smul r θ w]
  · rintro ⟨-, hlev⟩
    refine ⟨hφ.continuousOn.upperSemicontinuousOn, fun z w hdisc => ?_⟩
    set V := {ζ : ℂ | z + ζ • w ∈ U} with hV
    have hB : closedBall (0:ℂ) 1 ⊆ V := fun ζ hζ => hdisc ζ (by simpa using hζ)
    have hcont : Continuous fun θ => φ (z + circleMap 0 1 θ • w) :=
      hφ.continuousOn.comp_continuous
        (continuous_const.add ((continuous_circleMap 0 1).smul continuous_const))
        (fun θ => hdisc _ (by simp))
    refine ⟨hcont.intervalIntegrable 0 (2*π), ?_⟩
    have key := le_circleAverage_of_lap_nonneg (V := V) (g := fun ζ => φ (z + ζ • w))
      (G := Gc φ z w) (H := Hc φ z w) (fun ζ hζ => line_hasFDerivAt_g hU hφ z w hζ)
      (fun ζ hζ => line_hasFDerivAt_G hU hφ z w hζ) (line_contOn_H hU hφ z w) zero_le_one hB ?_
    · simpa using key
    · intro x hx θ
      rw [Hc_apply, Hc_apply]
      have := hlev _ (hB hx) (circleMap 0 1 θ • w)
      unfold levi at this
      rw [smul_smul, mul_comm Complex.I] at this
      linarith

end

end ReciprocityTheory.AnForm.A.PshLap

namespace ReciprocityTheory.AnForm.A.PshInh

open MeasureTheory Metric Set Filter Topology Real

noncomputable section

lemma ii_sup' {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ j, IntervalIntegrable (f j) volume a b) :
    IntervalIntegrable (fun θ => Finset.univ.sup' Finset.univ_nonempty (fun j => f j θ))
      volume a b := by
  have e : (fun θ => Finset.univ.sup' Finset.univ_nonempty (fun j => f j θ)) =
      Finset.univ.sup' Finset.univ_nonempty f := by
    funext θ; rw [Finset.sup'_apply]
  rw [e]
  refine Finset.sup'_induction _ _ (p := fun g => IntervalIntegrable g volume a b) ?_
    (fun j _ => hf j)
  intro g hg h hh
  exact ⟨hg.1.sup hh.1, hg.2.sup hh.2⟩

end

end ReciprocityTheory.AnForm.A.PshInh

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Set Filter Topology Real PshInh

theorem isPsh_iff_isLeviPsh_thm : IsPsh_iff_isLeviPshStatement := PshLap.plurisubharmonicIffLeviNonneg_holds

theorem isPsh_sup_thm : IsPsh_supStatement := by
  intro D ι _ _ U u hU hu
  refine ⟨?_, fun z w hdisc => ?_⟩
  · intro x hx y hy
    have : ∀ j, ∀ᶠ x' in 𝓝[U] x, u j x' < y := fun j =>
      (hu j).1 x hx y (lt_of_le_of_lt (Finset.le_sup' (fun j => u j x) (Finset.mem_univ j)) hy)
    filter_upwards [Filter.eventually_all.2 this] with x' hx'
    exact (Finset.sup'_lt_iff _).2 fun j _ => hx' j
  · have hci : ∀ j, CircleIntegrable (fun ζ : ℂ => u j (z + ζ • w)) 0 1 :=
      fun j => ((hu j).2 z w hdisc).1
    have hcs : CircleIntegrable (fun ζ : ℂ =>
        Finset.univ.sup' Finset.univ_nonempty (fun j => u j (z + ζ • w))) 0 1 :=
      ii_sup' (fun j θ => u j (z + circleMap 0 1 θ • w)) hci
    refine ⟨hcs, ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => u j z)
    simp only
    rw [hj]
    refine ((hu j).2 z w hdisc).2.trans (Real.circleAverage_mono (hci j) hcs fun ζ _ => ?_)
    exact Finset.le_sup' (fun j => u j (z + ζ • w)) (Finset.mem_univ j)

theorem isPsh_locallyIntegrable_thm : IsPsh_locallyIntegrableStatement :=
  PshMean.plurisubharmonicLocallyIntegrable_holds

theorem subMeanPolydisc_thm : SubMeanPolydiscStatement := PshMean.subMeanValuePolydisc_holds

theorem mollifierInhabit_thm : MollifierInhabitStatement := PshMol.circleInvariantMollifierExists_holds

end ReciprocityTheory.AnForm.A
end

