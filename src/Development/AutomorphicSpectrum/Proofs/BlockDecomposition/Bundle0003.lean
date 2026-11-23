module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CircleZero
section
noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace GlobalTheory.CompanionTheory.CfFJ

structure Fam {X : Type*} [TopologicalSpace X] (U : Set ℂ) (f : ℂ → X → ℂ) : Prop where
  cont : ContinuousOn (fun q : ℂ × X => f q.1 q.2) (U ×ˢ univ)
  hol : ∀ x, DifferentiableOn ℂ (f · x) U
  bd : ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ B : ℝ, ∀ w ∈ K, ∀ x, ‖f w x‖ ≤ B

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {U : Set ℂ}

theorem Fam.comp {f : ℂ → X → ℂ} (h : Fam U f) {φ : Z → X} (hφ : Continuous φ) : Fam U (fun w z => f w (φ z)) := by
  refine ⟨?_, fun z => h.hol (φ z), ?_⟩
  · exact h.cont.comp (continuous_fst.prodMk (hφ.comp continuous_snd)).continuousOn
      (fun q hq => ⟨hq.1, mem_univ _⟩)
  · intro K hK hc
    obtain ⟨B, hB⟩ := h.bd K hK hc
    exact ⟨B, fun w hw z => hB w hw (φ z)⟩

theorem Fam.slice {f : ℂ → X → ℂ} (h : Fam U f) {w : ℂ} (hw : w ∈ U) : Continuous (f w) :=
  h.cont.comp_continuous (f := fun x => (w, x)) (by fun_prop) (fun _ => ⟨hw, mem_univ _⟩)

variable [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y} {κ : Y → ℂ}

theorem Fam.swap [SFinite ν] {g : ℂ → Y → ℂ} (h : Fam U g) (hκ : Integrable κ ν) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hS : sphere c R ⊆ U) {a : ℂ → ℂ} (ha : ContinuousOn a (sphere c R)) :
    ∫ y, (∮ w in C(c, R), a w * g w y) * κ y ∂ν = ∮ w in C(c, R), a w * ∫ y, g w y * κ y ∂ν := by
  have cm : ∀ θ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR.le
  have hcm : Continuous (circleMap c R) := continuous_circleMap c R
  obtain ⟨A, hA⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn ha
  obtain ⟨B, hB⟩ := h.bd _ hS (isCompact_sphere c R)
  set Φ : ℝ → Y → ℂ := fun θ y => deriv (circleMap c R) θ • (a (circleMap c R θ) * g (circleMap c R θ) y) with hΦ
  have hΦc : Continuous fun q : Y × ℝ => Φ q.2 q.1 := by
    have h1 : Continuous fun q : Y × ℝ => g (circleMap c R q.2) q.1 :=
      h.cont.comp_continuous (f := fun q : Y × ℝ => (circleMap c R q.2, q.1))
        ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)
    have h2 : Continuous fun θ => a (circleMap c R θ) := ha.comp_continuous hcm cm
    have h3 : Continuous fun θ => deriv (circleMap c R) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 R).mul continuous_const
    simp only [hΦ, smul_eq_mul]
    exact (h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)
  have hΦb : ∀ θ y, ‖Φ θ y‖ ≤ |R| * (A * B) := by
    intro θ y
    simp only [hΦ, smul_eq_mul, norm_mul, deriv_circleMap, norm_circleMap_zero, Complex.norm_I, mul_one]
    have hb := hB _ (cm θ) y
    gcongr
    · exact (norm_nonneg _).trans (hA _ (cm θ))
    · exact hA _ (cm θ)
  have hint : Integrable (Function.uncurry fun (y : Y) (θ : ℝ) => Φ θ y * κ y)
      (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    have h0 : Integrable (fun q : Y × ℝ => κ q.1 * (1 : ℂ)) (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) :=
      hκ.mul_prod (integrable_const (1 : ℂ))
    have h1 := h0.bdd_mul (f := fun q : Y × ℝ => Φ q.2 q.1) (c := |R| * (A * B)) hΦc.aestronglyMeasurable
      (Eventually.of_forall fun q => hΦb _ _)
    refine h1.congr (Eventually.of_forall fun q => ?_)
    simp [Function.uncurry]
  have hpos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc ∫ y, (∮ w in C(c, R), a w * g w y) * κ y ∂ν
      = ∫ y, ∫ θ in Ioc 0 (2 * Real.pi), Φ θ y * κ y ∂volume ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [circleIntegral, intervalIntegral.integral_of_le hpos, integral_mul_const, hΦ]
    _ = ∫ θ in Ioc 0 (2 * Real.pi), ∫ y, Φ θ y * κ y ∂ν := integral_integral_swap hint
    _ = ∮ w in C(c, R), a w * ∫ y, g w y * κ y ∂ν := by
        simp only [circleIntegral, intervalIntegral.integral_of_le hpos]
        refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
        simp only [hΦ, smul_eq_mul, mul_assoc, integral_const_mul]

theorem Fam.stage [FirstCountableTopology X] [SFinite ν] (hU : IsOpen U) {f : ℂ → X × Y → ℂ} (h : Fam U f)
    (hκ : Integrable κ ν) : Fam U (fun w x => ∫ y, f w (x, y) * κ y ∂ν) := by
  have hsl : ∀ {w : ℂ}, w ∈ U → ∀ x, Continuous fun y => f w (x, y) := fun hw x =>
    (h.slice hw).comp (by fun_prop)
  have hcont : ContinuousOn (fun q : ℂ × X => ∫ y, f q.1 (q.2, y) * κ y ∂ν) (U ×ˢ univ) := by
    intro q hq
    have hqU : q.1 ∈ U := hq.1
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hqU)
    obtain ⟨B, hB⟩ := h.bd _ hrU (isCompact_closedBall _ _)
    have hnear : ∀ᶠ u : ℂ × X in 𝓝 q, u.1 ∈ ball q.1 r :=
      continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    refine ContinuousAt.continuousWithinAt (continuousAt_of_dominated (bound := fun y => B * ‖κ y‖) ?_ ?_ ?_ ?_)
    · filter_upwards [hnear] with u hu
      exact (hsl (hrU (ball_subset_closedBall hu)) u.2).aestronglyMeasurable.mul hκ.aestronglyMeasurable
    · filter_upwards [hnear] with u hu
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ (ball_subset_closedBall hu) _) (norm_nonneg _)
    · exact hκ.norm.const_mul B
    · refine Eventually.of_forall fun y => ?_
      have h1 : ContinuousAt (fun q : ℂ × (X × Y) => f q.1 q.2) (q.1, (q.2, y)) :=
        h.cont.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hqU, mem_univ _⟩)
      have h2 : ContinuousAt (fun u : ℂ × X => (u.1, (u.2, y))) q := by fun_prop
      exact (ContinuousAt.comp (f := fun u : ℂ × X => (u.1, (u.2, y))) h1 h2).mul continuousAt_const
  refine ⟨hcont, ?_, ?_⟩
  · intro x w₀ hw₀
    refine DifferentiableAt.differentiableWithinAt ?_
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hw₀)
    have hg : Fam U fun w y => f w (x, y) := h.comp (φ := fun y => (x, y)) (by fun_prop)
    have hS : sphere w₀ r ⊆ U := sphere_subset_closedBall.trans hrU
    have hQc : ContinuousOn (fun w => ∫ y, f w (x, y) * κ y ∂ν) U :=
      hcont.comp (Continuous.continuousOn (f := fun w : ℂ => (w, x)) (by fun_prop)) (fun w hw => ⟨hw, mem_univ _⟩)
    set Q : ℂ → ℂ := fun w => ∫ y, f w (x, y) * κ y ∂ν with hQ
    have hci : CircleIntegrable Q w₀ ((⟨r, hr.le⟩ : NNReal) : ℝ) := (hQc.mono hS).circleIntegrable hr.le
    have hps := hasFPowerSeriesOn_cauchy_integral hci (show (0 : NNReal) < ⟨r, hr.le⟩ from hr)
    refine hps.analyticAt.differentiableAt.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    have hwS : ∀ v ∈ sphere w₀ r, v ≠ w := by
      rintro v hv rfl
      exact (ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 hv)
    have hcauchy : ∀ y, ∮ v in C(w₀, r), ((2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹) * f v (x, y) = f w (x, y) := by
      intro y
      have h1 := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (s := ∅) countable_empty hw
        (f := fun v => f v (x, y)) ((hg.hol y).continuousOn.mono hrU)
        (fun v hv => (hg.hol y).differentiableAt (hU.mem_nhds (hrU (ball_subset_closedBall hv.1))))
      simp only [smul_eq_mul] at h1
      simp only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]
      rw [h1, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
    have hsw := hg.swap hκ hr hS (a := fun v => (2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹)
      (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun v hv => sub_ne_zero.2 (hwS v hv)))
    simp only [hcauchy] at hsw
    simp only [smul_eq_mul]
    change Q w = _
    rw [hQ]
    simp only
    rw [hsw]
    simp only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]
    rfl
  · intro K hK hc
    obtain ⟨B, hB⟩ := h.bd K hK hc
    refine ⟨∫ y, B * ‖κ y‖ ∂ν, fun w hw x => ?_⟩
    refine norm_integral_le_of_norm_le (hκ.norm.const_mul B) (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB w hw _) (norm_nonneg _)

theorem circle_cont {e : ℂ → Z → ℂ} (hc : ContinuousOn (fun q : ℂ × Z => e q.1 q.2) (U ×ˢ univ)) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hS : sphere c R ⊆ U) {a : ℂ → ℂ} (ha : ContinuousOn a (sphere c R)) :
    Continuous fun z => ∮ w in C(c, R), a w * e w z := by
  have cm : ∀ θ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR
  have hcm : Continuous (circleMap c R) := continuous_circleMap c R
  have h1 : Continuous fun q : Z × ℝ => e (circleMap c R q.2) q.1 :=
    hc.comp_continuous (f := fun q : Z × ℝ => (circleMap c R q.2, q.1))
      ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)
  have h2 : Continuous fun θ => a (circleMap c R θ) := ha.comp_continuous hcm cm
  have h3 : Continuous fun θ => deriv (circleMap c R) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  simp only [circleIntegral]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  simp only [Function.uncurry_def, smul_eq_mul]
  exact (h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)

theorem circle_zero {e : ℂ → ℂ} (hU : IsOpen U) (he : DifferentiableOn ℂ e U) {d : Polynomial ℂ} (hd : d ≠ 0) {s₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hB : closedBall s₀ ε ⊆ U) (hroot : ∀ z ∈ closedBall s₀ ε, z ≠ s₀ → d.eval z ≠ 0) {j : ℕ}
    (hj : d.rootMultiplicity s₀ ≤ j) : ∮ z in C(s₀, ε), (z - s₀) ^ j * (e z / d.eval z) = 0 := by
  obtain ⟨q, hq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd s₀
  set m := d.rootMultiplicity s₀ with hm
  have hev : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z := fun z => by
    conv_lhs => rw [hq]
    simp
  have hq0 : ∀ z ∈ closedBall s₀ ε, q.eval z ≠ 0 := by
    intro z hz h0
    by_cases hzs : z = s₀
    · subst hzs
      exact hnd (Polynomial.dvd_iff_isRoot.2 h0)
    · exact hroot z hz hzs (by rw [hev, h0, mul_zero])
  have hsub : ∀ z ∈ sphere s₀ ε, z ≠ s₀ := by
    rintro z hz rfl
    simp [hε.ne] at hz
  have hcongr : ∮ z in C(s₀, ε), (z - s₀) ^ j * (e z / d.eval z) =
      ∮ z in C(s₀, ε), (z - s₀) ^ (j - m) * (e z / q.eval z) := by
    refine circleIntegral.integral_congr hε.le fun z hz => ?_
    have h1 : z - s₀ ≠ 0 := sub_ne_zero.2 (hsub z hz)
    have h2 := hq0 z (sphere_subset_closedBall hz)
    rw [hev, show j = (j - m) + m by omega, pow_add, Nat.add_sub_cancel]
    field_simp
  rw [hcongr]
  have hdiff : ∀ z ∈ closedBall s₀ ε, DifferentiableAt ℂ (fun z => (z - s₀) ^ (j - m) * (e z / q.eval z)) z := by
    intro z hz
    have h1 : DifferentiableAt ℂ e z := he.differentiableAt (hU.mem_nhds (hB hz))
    have h2 : DifferentiableAt ℂ (fun z => q.eval z) z := q.differentiable.differentiableAt
    exact ((differentiableAt_id.sub_const s₀).pow _).mul (h1.div h2 (hq0 z hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le countable_empty
    (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z (ball_subset_closedBall hz.1))

end GlobalTheory.CompanionTheory.CfFJ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffIntegralDensity
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothParam

variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def pderiv (H : P × Y → F) : P × Y → (P →L[ℝ] F) :=
  fun z => fderiv ℝ (fun q => H (q, z.2)) z.1

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma hasFDerivAt_partial {H : P × Y → F} (hH : Differentiable ℝ H) (p : P) (y : Y) :
    HasFDerivAt (fun q => H (q, y))
      ((fderiv ℝ H (p, y)).comp (ContinuousLinearMap.inl ℝ P Y)) p :=
  (hH (p, y)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p y)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma pderiv_eq {H : P × Y → F} (hH : Differentiable ℝ H) :
    pderiv H = fun z => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P Y) := by
  funext z
  exact (hasFDerivAt_partial hH z.1 z.2).fderiv

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma contDiff_pderiv {H : P × Y → F} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (pderiv H) := by
  rw [pderiv_eq (hH.differentiable (by simp))]
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact h1.clm_comp contDiff_const

omit [FiniteDimensional ℝ P] [NormedSpace ℝ P] [FiniteDimensional ℝ Y] [NormedSpace ℝ Y] in
lemma integrable_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) {H : P × Y → F} (hH : Continuous H) (p : P) :
    Integrable (fun x => u x • H (p, ψ x)) ν := by
  obtain ⟨C, hC⟩ := (isCompact_singleton.prod hK).exists_bound_of_continuousOn
    (f := H) (s := {p} ×ˢ K) hH.continuousOn
  have hc : Continuous fun y => H (p, y) := hH.comp (by fun_prop)
  have meas : AEStronglyMeasurable (fun x => u x • H (p, ψ x)) ν :=
    hu.aestronglyMeasurable.smul (hc.comp_aestronglyMeasurable hψ)
  refine (hu.norm.mul_const C).mono' meas ?_
  filter_upwards [hψK] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC _ ⟨rfl, hx⟩) (norm_nonneg _)

theorem hasFDerivAt_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
      (∫ x, u x • pderiv H (p₀, ψ x) ∂ν) p₀ := by
  have hd : Differentiable ℝ H := hH.differentiable (by simp)
  have hc' : Continuous (pderiv H) := (contDiff_pderiv hH).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hK).exists_bound_of_continuousOn
    (f := pderiv H) hc'.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p x => u x • H (p, ψ x)) (F' := fun p x => u x • pderiv H (p, ψ x))
    (bound := fun x => ‖u x‖ * C) (s := Metric.closedBall p₀ 1)
    (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun p =>
      (integrable_weight hu hψ hK hψK hH.continuous p).aestronglyMeasurable
  · exact integrable_weight hu hψ hK hψK hH.continuous p₀
  · exact (integrable_weight hu hψ hK hψK hc' p₀).aestronglyMeasurable
  · filter_upwards [hψK] with x hx p hp
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ⟨hp, hx⟩) (norm_nonneg _)
  · exact hu.norm.mul_const C
  · refine Eventually.of_forall fun x p _ => ?_
    have h1 : HasFDerivAt (fun q => H (q, ψ x)) (pderiv H (p, ψ x)) p :=
      ((hasFDerivAt_partial hd p (ψ x)).differentiableAt).hasFDerivAt
    exact h1.const_smul (u x)

theorem contDiff_weight_nat {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (H : P × Y → F),
      ContDiff ℝ ∞ H → ContDiff ℝ n (fun p => ∫ x, u x • H (p, ψ x) ∂ν) := by
  induction n with
  | zero =>
    intro F _ _ _ H hH
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_weight hu hψ hK hψK hH p).continuousAt
  | succ n ih =>
    intro F _ _ _ H hH
    have hfd : fderiv ℝ (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
        = fun p => ∫ x, u x • pderiv H (p, ψ x) ∂ν := by
      funext p
      exact (hasFDerivAt_weight hu hψ hK hψK hH p).fderiv
    have : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [this, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_weight hu hψ hK hψK hH p).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (P →L[ℝ] F) (pderiv H) (contDiff_pderiv hH)

theorem contDiff_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p => ∫ x, u x • H (p, ψ x) ∂ν) :=
  contDiff_infty.2 fun n => contDiff_weight_nat hu hψ hK hψK n F H hH

theorem contDiff_integral_density (Ω P Y : Type) [MeasurableSpace Ω] [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (ν : Measure Ω) (w : Ω → ℂ) (ψ : Ω → Y) (K : Set Y)
    (hw : Integrable w ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (h : P × Y → ℂ) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p => ∫ x, h (p, ψ x) * w x ∂ν) ∧
      ∀ p v, fderiv ℝ (fun q => ∫ x, h (q, ψ x) * w x ∂ν) p v
        = ∫ x, fderiv ℝ (fun q => h (q, ψ x)) p v * w x ∂ν := by
  have hu₁ : Integrable (fun x => (w x).re) ν := hw.re
  have hu₂ : Integrable (fun x => (w x).im) ν := hw.im
  set h₂ : P × Y → ℂ := fun z => Complex.I * h z with hh₂def
  have hh₂ : ContDiff ℝ ∞ h₂ := contDiff_const.mul hh
  have hdec : ∀ (a b : ℂ), a * b = b.re • a + b.im • (Complex.I * a) := by
    intro a b
    apply Complex.ext <;> simp <;> ring
  have hsplit : (fun p => ∫ x, h (p, ψ x) * w x ∂ν)
      = fun p => (∫ x, (w x).re • h (p, ψ x) ∂ν) + ∫ x, (w x).im • h₂ (p, ψ x) ∂ν := by
    funext p
    rw [← integral_add (integrable_weight hu₁ hψ hK hψK hh.continuous p)
      (integrable_weight hu₂ hψ hK hψK hh₂.continuous p)]
    exact integral_congr_ae (Eventually.of_forall fun x => hdec _ _)
  refine ⟨?_, fun p v => ?_⟩
  · rw [hsplit]
    exact (contDiff_weight hu₁ hψ hK hψK hh).add (contDiff_weight hu₂ hψ hK hψK hh₂)
  · have hd : Differentiable ℝ h := hh.differentiable (by simp)
    have hD := (hasFDerivAt_weight hu₁ hψ hK hψK hh p).add
      (hasFDerivAt_weight hu₂ hψ hK hψK hh₂ p)
    have hfd := hD.fderiv
    have hi₁ := integrable_weight hu₁ hψ hK hψK (contDiff_pderiv hh).continuous p
    have hi₂ := integrable_weight hu₂ hψ hK hψK (contDiff_pderiv hh₂).continuous p
    have hp₂ : ∀ y, pderiv h₂ (p, y) v = Complex.I * pderiv h (p, y) v := by
      intro y
      have h1 : HasFDerivAt (fun q => h (q, y)) (pderiv h (p, y)) p :=
        ((hasFDerivAt_partial hd p y).differentiableAt).hasFDerivAt
      have h2 : HasFDerivAt (fun q => h₂ (q, y)) (Complex.I • pderiv h (p, y)) p := by
        exact h1.const_smul Complex.I
      have : pderiv h₂ (p, y) = Complex.I • pderiv h (p, y) := h2.fderiv
      rw [this]; simp
    rw [hsplit]
    change fderiv ℝ ((fun p => ∫ x, (w x).re • h (p, ψ x) ∂ν) +
      (fun p => ∫ x, (w x).im • h₂ (p, ψ x) ∂ν)) p v = _
    rw [hfd, ContinuousLinearMap.add_apply, ContinuousLinearMap.integral_apply hi₁,
      ContinuousLinearMap.integral_apply hi₂,
      ← integral_add (hi₁.apply_continuousLinearMap v) (hi₂.apply_continuousLinearMap v)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.smul_apply]
    rw [hp₂]
    exact (hdec _ _).symm

end GlobalTheory.CompanionTheory.SmoothParam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIteratedDerivHolomorphicFamily
section
open Topology Filter

namespace GlobalTheory.CompanionTheory.HolFamily

theorem continuous_iteratedDeriv_family :
    ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U →
      (∀ g, DifferentiableOn ℂ (Ê · g) U) →
      ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
      ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  intro G _ U E hU hd hc z hz j
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hU z hz
  have hr : 0 < R / 2 := by positivity
  have hcl : Metric.closedBall z (R / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  rw [continuous_iff_continuousAt]
  intro g0
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hrj : 0 < (R / 2) ^ j := pow_pos hr j
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε * (R / 2) ^ j / (2 * (j.factorial : ℝ)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have htube : ∀ᶠ g in 𝓝 g0, ∀ w ∈ Metric.sphere z (R / 2), ‖E w g - E w g0‖ < δ := by
    refine (isCompact_sphere z (R / 2)).eventually_forall_of_forall_eventually
      (P := fun g w => ‖E w g - E w g0‖ < δ) ?_
    intro w hw
    have hwU : w ∈ U := hcl (Metric.sphere_subset_closedBall hw)
    have hcont : ContinuousAt (fun y : ℂ × G => E y.1 y.2) (w, g0) :=
      hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hwU, trivial⟩)
    have hA : ContinuousAt (fun p : G × ℂ => E p.2 p.1) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, p.1))
        (g := fun y : ℂ × G => E y.1 y.2) hcont continuous_swap.continuousAt
    have hB : ContinuousAt (fun p : G × ℂ => E p.2 g0) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, g0))
        (g := fun y : ℂ × G => E y.1 y.2) hcont (by fun_prop)
    have hN : ContinuousAt (fun p : G × ℂ => ‖E p.2 p.1 - E p.2 g0‖) (g0, w) := (hA.sub hB).norm
    have hlt : ‖E w g0 - E w g0‖ < δ := by simpa using hδ
    exact hN.eventually_lt continuousAt_const hlt
  filter_upwards [htube] with g hg
  have hzn : U ∈ 𝓝 z := hU.mem_nhds hz
  have h1 : ContDiffAt ℂ j (E · g) z := ((hd g).analyticAt hzn).contDiffAt
  have h2 : ContDiffAt ℂ j (E · g0) z := ((hd g0).analyticAt hzn).contDiffAt
  rw [dist_eq_norm, ← iteratedDeriv_fun_sub h1 h2]
  have hdc : DiffContOnCl ℂ (fun x => E x g - E x g0) (Metric.ball z (R / 2)) :=
    ((hd g).sub (hd g0)).diffContOnCl_ball hcl
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := δ) j hr hdc
    (fun w hw => (hg w hw).le)
  refine hb.trans_lt ?_
  have : (j.factorial : ℝ) * δ / (R / 2) ^ j = ε / 2 := by
    rw [hδdef]; field_simp
  rw [this]
  linarith

end GlobalTheory.CompanionTheory.HolFamily
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariant
section
open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

theorem sum_add_eq_sum_of_transversal : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  intro X _ M _ A H hHA T hTA huniq F hF a ha
  classical
  have hex : ∀ t ∈ T, ∃ t', t' ∈ T ∧ (t + a) - t' ∈ H := fun t ht =>
    (huniq (t + a) (A.add_mem (hTA t ht) ha)).exists
  choose! g hgT hgH using hex
  have uniq : ∀ x ∈ A, ∀ t₁ t₂, t₁ ∈ T → x - t₁ ∈ H → t₂ ∈ T → x - t₂ ∈ H → t₁ = t₂ :=
    fun x hx t₁ t₂ h1 h1' h2 h2' => (huniq x hx).unique ⟨h1, h1'⟩ ⟨h2, h2'⟩
  refine Finset.sum_bij (fun t _ => g t) (fun t ht => hgT t ht) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ heq
    have hd : t₁ - t₂ ∈ H := by
      have h3 := H.sub_mem (hgH t₁ h₁) (hgH t₂ h₂)
      have e : t₁ + a - g t₁ - (t₂ + a - g t₂) = t₁ - t₂ := by rw [heq]; abel
      rwa [e] at h3
    exact uniq t₁ (hTA t₁ h₁) t₁ t₂ h₁ (by rw [sub_self]; exact H.zero_mem) h₂ hd
  · intro t' ht'
    obtain ⟨t, ⟨htT, htH⟩, -⟩ := huniq (t' - a) (A.sub_mem (hTA t' ht') ha)
    refine ⟨t, htT, ?_⟩
    have h1 : t + a - t' ∈ H := by
      have h3 := H.neg_mem htH
      have e : -(t' - a - t) = t + a - t' := by abel
      rwa [e] at h3
    exact uniq (t + a) (A.add_mem (hTA t htT) ha) (g t) t' (hgT t htT) (hgH t htT) ht' h1
  · intro t ht
    have h3 := hF (g t) _ (hgH t ht)
    have e : g t + (t + a - g t) = t + a := by abel
    rw [e] at h3
    exact h3

end GlobalTheory.CompanionTheory.Transversal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableOfNumberField
section
namespace GlobalTheory.CompanionTheory.NumberFieldMatrix

theorem countable_of_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_matrix (E : Type) [Field E] [NumberField E] (m n : ℕ) :
    Countable (Matrix (Fin m) (Fin n) E) := by
  haveI := GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_of_numberField E
  exact inferInstanceAs (Countable (Fin m → Fin n → E))

theorem matrix_countable :
    ∀ (E : Type) [Field E] [NumberField E] (m n : ℕ),
      Countable (Matrix (Fin m) (Fin n) E) :=
  fun E _ _ m n => countable_matrix E m n

end GlobalTheory.CompanionTheory.NumberFieldMatrix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteCosetsPrincipalCongruence
section
namespace GlobalTheory.CompanionTheory.Congruence

open Matrix

theorem finite_quotient_span_pow (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (ϖ : R) (m : ℕ) (hϖ : Irreducible ϖ) :
    Finite (R ⧸ Ideal.span {ϖ ^ m}) := by
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    (inferInstance : Finite (IsLocalRing.ResidueField R))
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m

end GlobalTheory.CompanionTheory.Congruence
end

