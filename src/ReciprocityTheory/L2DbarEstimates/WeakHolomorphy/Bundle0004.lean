module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCutB
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCut
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal Manifold

noncomputable section

variable {n : ℕ}

lemma norm_sq_clm (L : V n →L[ℂ] ℂ) :
    ‖L‖ ^ 2 = ∑ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2 := by

  set v : V n := (InnerProductSpace.toDual ℂ (V n)).symm L with hv
  have hL : ‖L‖ = ‖v‖ := by
    rw [hv, LinearIsometryEquiv.norm_map]
  have hco : ∀ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ = ‖v j‖ := by
    intro j
    rw [← InnerProductSpace.toDual_symm_apply, ← hv, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right]
    simp
  rw [hL, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [hco]

lemma grad_log_sq {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (h0 : F z ≠ 0) :
    ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2 ≤
      4 * (∑ j, ‖fderiv ℂ F z (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2) / ‖F z‖ ^ 2 := by
  have hDa : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hpos : 0 < ‖F z‖ := norm_pos_iff.mpr h0
  have h1 : HasFDerivAt F ((fderiv ℂ F z).restrictScalars ℝ) z :=
    hDa.hasFDerivAt.restrictScalars ℝ
  have h2 := h1.norm_sq
  have h3 := h2.log (by positivity)
  rw [← norm_sq_clm, h3.fderiv]
  set D := fderiv ℂ F z

  have hM : ‖(‖F z‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (F z)).comp (D.restrictScalars ℝ))‖ ≤
      2 * ‖D‖ / ‖F z‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    have hi : |inner ℝ (F z) (D h)| ≤ ‖F z‖ * (‖D‖ * ‖h‖) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm h) (norm_nonneg _))
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul,
      Real.norm_eq_abs, abs_mul, abs_inv, Nat.cast_ofNat]
    rw [abs_of_pos (by positivity : (0:ℝ) < ‖F z‖ ^ 2), abs_two]
    calc (‖F z‖ ^ 2)⁻¹ * (2 * |inner ℝ (F z) (D h)|)
        ≤ (‖F z‖ ^ 2)⁻¹ * (2 * (‖F z‖ * (‖D‖ * ‖h‖))) := by gcongr
      _ = 2 * ‖D‖ / ‖F z‖ * ‖h‖ := by field_simp
  calc _ ≤ (2 * ‖D‖ / ‖F z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hM 2
    _ = 4 * ‖D‖ ^ 2 / ‖F z‖ ^ 2 := by ring

end

theorem ext_cut {n : ℕ} {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {K : Set (V n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ k : ℝ, 1 ≤ k →
      ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k},
        ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤ C * ENNReal.ofReal (k ^ 2) := by
  classical
  obtain ⟨δ0, hδ0, hδ0Ω⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  set δ := δ0 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set T := cthickening δ K with hTdef
  have hT : IsCompact T := hK.cthickening
  have hTΩ : T ⊆ Ω := (cthickening_mono (by linarith) K).trans hδ0Ω
  have hball : ∀ z ∈ T, closedBall z δ ⊆ cthickening δ0 K := fun z hz =>
    (closedBall_subset_cthickening hz δ).trans
      ((cthickening_cthickening_subset hδ.le hδ.le K).trans (by rw [hδdef]; ring_nf; rfl))
  obtain ⟨M0, hM0⟩ := (hK.cthickening (r := δ0)).exists_bound_of_continuousOn
    (hF.continuousOn.mono hδ0Ω)
  set M := max M0 0
  have hM : ∀ z ∈ cthickening δ0 K, ‖F z‖ ≤ M := fun z hz => (hM0 z hz).trans (le_max_left _ _)
  have hM0' : 0 ≤ M := le_max_right _ _

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed (𝓘(ℝ, V n)) (n := 2)
    (isOpen_thickening (δ := δ) (E := K)).isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.2 (self_subset_thickening hδ K))
  set ψ : V n → ℝ := ⇑f with hψdef
  have hψ : ContDiff ℝ 2 ψ := by
    have := contMDiff_iff_contDiff.1 f.contMDiff
    exact_mod_cast this
  have hψT : tsupport ψ ⊆ T := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    by_contra h
    exact hx (hf0 h)
  have hψ1 : ∀ z ∈ K, ψ z = 1 := fun z hz => hf1 hz
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => (hf01 z).1

  set b := EuclideanSpace.basisFun (Fin n) ℂ
  have hb1 : ∀ j, ‖b j‖ = 1 := fun j => b.orthonormal.1 j
  have hcau : ∀ j, ∀ z ∈ T, ‖fderiv ℂ F z (b j)‖ ≤ M / δ ∧ ‖complexLineSecondDeriv F z (b j)‖ ≤ 4 * M / δ ^ 2 :=
    fun j z hz => cauchy_line hΩ hF (hb1 j) hδ ((hball z hz).trans hδ0Ω)
      (fun w hw => hM w (hball z hz hw))
  have hMT : ∀ z ∈ T, ‖F z‖ ≤ M := fun z hz => hM z (hball z hz (mem_closedBall_self hδ.le))
  set D : Fin n → ℂ → V n → ℝ := fun j μ z =>
    fderiv ℝ (fun w => fderiv ℝ ψ w (μ • b j)) z (μ • b j) with hDdef
  set C0 : ℝ := 4 * (∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|)) * ((M ^ 2 + 2) ^ 2 / 2) with hC0def
  have hC0 : 0 ≤ C0 := by
    have : 0 ≤ ∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|) :=
      Finset.sum_nonneg fun j _ => add_nonneg (integral_nonneg fun _ => abs_nonneg _)
        (integral_nonneg fun _ => abs_nonneg _)
    positivity
  refine ⟨ENNReal.ofReal C0, ENNReal.ofReal_lt_top, fun k hk => ?_⟩
  set ε := Real.exp (-2 * k) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have gr : ∀ j, ∀ μ : ℂ, ‖μ‖ = 1 → _ := fun j μ hμ =>
    green_dir hΩ hF hT hTΩ hψ hψT hε (b j) μ hμ hMT (fun z hz => (hcau j z hz).1)
      (fun z hz => (hcau j z hz).2)
  have g1 := fun j => gr j 1 norm_one
  have gI := fun j => gr j I Complex.norm_I
  have hQi : ∀ j, Integrable (fun z => ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I)) := fun j => (g1 j).1.add (gI j).1
  have hGi : Integrable (fun z => ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) := integrable_finsetSum _ fun j _ => hQi j
  have hGeq : ∀ z, (∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) = ψ z * (4 * (‖F z‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) +
        halfLogRatioSqDeriv ε (‖F z‖ ^ 2)) * ∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) := by
    intro z
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, lineSecondVariation_add_I]
    ring
  have hG0 : ∀ z, 0 ≤ ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I)) := fun z => by
    rw [hGeq z]
    have := cut_rho_nonneg hε (by positivity : (0 : ℝ) ≤ ‖F z‖ ^ 2)
    exact mul_nonneg (hψ0 z) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => by positivity))
  have hIG : (∫ z, ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) = ∑ j, ((∫ z, D j 1 z * cutP ε (‖F z‖ ^ 2)) +
        ∫ z, D j I z * cutP ε (‖F z‖ ^ 2)) := by
    rw [integral_finsetSum _ fun j _ => hQi j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add (g1 j).1 (gI j).1]
    exact congrArg₂ (· + ·) (g1 j).2.2.2.2 (gI j).2.2.2.2
  have hDb : ∀ j, ∀ μ : ℂ, ‖μ‖ = 1 → ∫ z, D j μ z * cutP ε (‖F z‖ ^ 2) ≤
      (∫ z, |D j μ z|) * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) := by
    intro j μ hμ
    obtain ⟨_, hi, hiD, hz0, _⟩ := gr j μ hμ
    rw [← integral_mul_const]
    refine integral_mono hi (hiD.abs.mul_const _) (fun z => ?_)
    by_cases hz : z ∈ T
    · have h1 : cutP ε (‖F z‖ ^ 2) ≤ (M ^ 2 + 2) ^ 2 / 2 * k ^ 2 :=
        (cutP_mono hε (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (hMT z hz) 2)).trans
          (cutP_le hk (by positivity))
      have h2 := polydiscCutoff_nonneg ε (‖F z‖ ^ 2)
      calc D j μ z * cutP ε (‖F z‖ ^ 2) ≤ |D j μ z| * cutP ε (‖F z‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |D j μ z| * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · have : D j μ z = 0 := hz0 z hz
      simp [this]
  have hbound : 4 * (∫ z, ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) ≤ C0 * k ^ 2 := by
    rw [hIG, hC0def]
    have : ∑ j, ((∫ z, D j 1 z * cutP ε (‖F z‖ ^ 2)) + ∫ z, D j I z * cutP ε (‖F z‖ ^ 2)) ≤
        ∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|) * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) :=
      Finset.sum_le_sum fun j _ => by
        rw [add_mul]; exact add_le_add (hDb j 1 norm_one) (hDb j I Complex.norm_I)
    rw [← Finset.sum_mul] at this
    nlinarith
  have hpt : ∀ z ∈ K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k},
      ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
          (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
          (complexLineSecondDeriv F z (b j) * I * I))) := by
    rintro z ⟨hzK, hz0, -, hz2⟩
    have hzΩ := hKΩ hzK
    have hF0 : 0 < ‖F z‖ := norm_pos_iff.2 hz0
    have hs0 : 0 < ‖F z‖ ^ 2 := by positivity
    have hεs : ε ≤ ‖F z‖ ^ 2 := by
      rw [hεdef, ← Real.exp_log hs0]
      exact Real.exp_le_exp.2 (by linarith)
    have hg := grad_log_sq hΩ hF hzΩ hz0
    have hr := cut_rho_ge hε hεs
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hGeq z, hψ1 z hzK, one_mul]
    have hsum : 0 ≤ ∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
    calc ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2
        ≤ 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) / ‖F z‖ ^ 2 := hg
      _ = 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) * (‖F z‖ ^ 2)⁻¹ := by ring
      _ ≤ 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) *
          (4 * (‖F z‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) + halfLogRatioSqDeriv ε (‖F z‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  have hGi4 := hGi.const_mul 4
  calc ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}, ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2
      ≤ ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}, ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) :=
        setLIntegral_mono_ae hGi4.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
          (Eventually.of_forall hpt)
    _ ≤ ∫⁻ z, ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ z, 4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) :=
        (ofReal_integral_eq_lintegral_ofReal hGi4
          (Eventually.of_forall fun z => mul_nonneg (by norm_num) (hG0 z))).symm
    _ ≤ ENNReal.ofReal (C0 * k ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul]
        exact hbound
    _ = ENNReal.ofReal C0 * ENNReal.ofReal (k ^ 2) := ENNReal.ofReal_mul hC0

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem moll_eq_zero_of_lt {n : ℕ} {t : ℝ} (ht : 0 < t) {z : V n} (hz : t / 2 < ‖z‖) :
    moll n t z = 0 := by
  have h1 : 1 - 4 * (‖z‖ / t) ^ 2 ≤ 0 := by
    have h2 : 1 / 2 < ‖z‖ / t := by
      rw [lt_div_iff₀ ht]; linarith
    nlinarith
  simp only [moll, mollProf, bumpProf, Real.smoothTransition.zero_of_nonpos h1, mul_zero]

private theorem integral_circleMap_smul_eq_two_pi_mul {n : ℕ} {a : ℝ} {h : V n → ℂ} {x z : V n}
    (hh : DifferentiableOn ℂ h (ball x a)) (hz : ‖z‖ < a) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, h (x + circleMap 0 1 θ • z) = 2 * Real.pi * h x := by
  have hd : DifferentiableOn ℂ (fun l : ℂ => h (x + l • z)) (closedBall (0 : ℂ) 1) := by
    intro l hl
    have hl1 : ‖l‖ ≤ 1 := by simpa using hl
    have hmem : x + l • z ∈ ball x a := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      calc ‖l‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hl1 (norm_nonneg z)
        _ < a := by rw [one_mul]; exact hz
    have h1 : DifferentiableAt ℂ h (x + l • z) := hh.differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun l : ℂ => x + l • z) l :=
      (differentiableAt_id.smul_const z).const_add x
    exact (h1.comp l h2).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun l : ℂ => h (x + l • z)) (ball (0 : ℂ) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hd
  have hC := hdc.circleIntegral_sub_inv_smul (mem_ball_self one_pos)
  have e0 : h (x + (0 : ℂ) • z) = h x := by rw [zero_smul, add_zero]
  have key : Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi, h (x + circleMap 0 1 θ • z)
      = 2 * Real.pi * Complex.I * h x := by
    calc Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi, h (x + circleMap 0 1 θ • z)
        = ∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap 0 1) θ •
            ((circleMap 0 1 θ - 0)⁻¹ • h (x + circleMap 0 1 θ • z)) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun θ _ => ?_
          have hne : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
          simp only [deriv_circleMap, sub_zero, smul_eq_mul]
          first
          | (rw [mul_comm (circleMap 0 1 θ) Complex.I, mul_assoc, mul_inv_cancel_left₀ hne])
          | field_simp
          | (field_simp; ring)
      _ = ∮ l in C(0, 1), (l - 0)⁻¹ • h (x + l • z) := rfl
      _ = (2 * Real.pi * Complex.I : ℂ) • h (x + (0 : ℂ) • z) := hC
      _ = 2 * Real.pi * Complex.I * h x := by rw [e0, smul_eq_mul]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  rw [key]
  ring

private theorem integral_comp_smul_of_norm_eq_one {n : ℕ} (c : ℂ) (hc : ‖c‖ = 1) (f : V n → ℂ) :
    ∫ z, f (c • z) = ∫ z, f z := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  let e : V n ≃ₗᵢ[ℝ] V n :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ (V n) c hc0).restrictScalars ℝ
      norm_map' := fun z => by
        show ‖c • z‖ = ‖z‖
        rw [norm_smul, hc, one_mul] }
  show ∫ z, f (e z) = ∫ z, f z
  exact e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding f

private theorem moll_eq_zero_of_half_lt_norm {n : ℕ} {t : ℝ} (ht : 0 < t) {z : V n} (hz : t / 2 < ‖z‖) :
    moll n t z = 0 := by
  have h1 : 1 - 4 * (‖z‖ / t) ^ 2 ≤ 0 := by
    have h2 : 1 / 2 < ‖z‖ / t := by
      rw [lt_div_iff₀ ht]; linarith
    nlinarith
  simp only [moll, mollProf, bumpProf, Real.smoothTransition.zero_of_nonpos h1, mul_zero]

private theorem integrable_moll (n : ℕ) {t : ℝ} (ht : 0 < t) : Integrable (moll n t) :=
  (moll_contDiff n t).continuous.integrable_of_hasCompactSupport (moll_hasCompactSupport n ht)

private theorem integral_moll_mul_eq_of_differentiableOn_ball {n : ℕ} {a : ℝ} (ha : 0 < a) {h : V n → ℂ} {x : V n}
    (hh : DifferentiableOn ℂ h (ball x a)) :
    ∫ w, (moll n a (x - w) : ℂ) * h w = h x := by
  have hA : ∫ w, (moll n a (x - w) : ℂ) * h w = ∫ z, (moll n a z : ℂ) * h (x + z) := by
    have e1 := integral_add_left_eq_self (μ := volume) (fun w => (moll n a (x - w) : ℂ) * h w) x
    simpa only [moll, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg] using e1.symm
  rw [hA]
  have hB : ∀ θ : ℝ, ∫ z, (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z)
      = ∫ z, (moll n a z : ℂ) * h (x + z) := by
    intro θ
    have hc : ‖circleMap 0 1 θ‖ = 1 := by simp
    have e2 := integral_comp_smul_of_norm_eq_one (circleMap 0 1 θ) hc (fun z => (moll n a z : ℂ) * h (x + z))
    simpa only [moll, norm_smul, hc, one_mul] using e2
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (a / 2)).exists_bound_of_continuousOn
    (hh.continuousOn.mono (closedBall_subset_ball (by linarith)))
  have hcont : Continuous (fun p : ℝ × V n => (moll n a p.2 : ℂ) * h (x + circleMap 0 1 p.1 • p.2)) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨θ0, z0⟩
    by_cases hz0 : ‖z0‖ < a
    · have hmc : Continuous fun p : ℝ × V n => (moll n a p.2 : ℂ) :=
        Complex.continuous_ofReal.comp ((moll_contDiff n a).continuous.comp continuous_snd)
      have hg : Continuous fun p : ℝ × V n => x + circleMap 0 1 p.1 • p.2 :=
        continuous_const.add (((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd)
      have hmem : x + circleMap 0 1 θ0 • z0 ∈ ball x a := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_circleMap_zero, abs_one,
          one_mul]
        exact hz0
      have hhc : ContinuousAt h (x + circleMap 0 1 θ0 • z0) :=
        (hh.differentiableAt (isOpen_ball.mem_nhds hmem)).continuousAt
      exact hmc.continuousAt.mul (hhc.comp_of_eq hg.continuousAt rfl)
    · push_neg at hz0
      have hopen : IsOpen {p : ℝ × V n | a / 2 < ‖p.2‖} :=
        isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
      have hmem : (θ0, z0) ∈ {p : ℝ × V n | a / 2 < ‖p.2‖} := by
        show a / 2 < ‖z0‖
        linarith
      have hev : (fun p : ℝ × V n => (moll n a p.2 : ℂ) * h (x + circleMap 0 1 p.1 • p.2))
          =ᶠ[𝓝 (θ0, z0)] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds hmem] with p hp
        rw [moll_eq_zero_of_half_lt_norm ha hp]
        simp
      exact (continuousAt_congr hev).mpr continuousAt_const
  have hInt : Integrable
      (Function.uncurry fun (θ : ℝ) (z : V n) => (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z))
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) := by
    have hg1 : Integrable (fun _ : ℝ => C) (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
      integrable_const C
    have hbd : Integrable (fun p : ℝ × V n => C * |moll n a p.2|)
        ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) := by
      first
      | exact MeasureTheory.Integrable.prod_mul hg1 (integrable_moll n ha).abs
      | exact MeasureTheory.Integrable.mul_prod hg1 (integrable_moll n ha).abs
      | exact MeasureTheory.Integrable.prod_smul hg1 (integrable_moll n ha).abs
      | exact MeasureTheory.Integrable.comp_snd ((integrable_moll n ha).abs.const_mul C) _
      | exact ((integrable_moll n ha).abs.const_mul C).comp_snd
    refine Integrable.mono' hbd
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    show ‖(moll n a p.2 : ℂ) * h (x + circleMap 0 1 p.1 • p.2)‖ ≤ C * |moll n a p.2|
    by_cases hp : ‖p.2‖ ≤ a / 2
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply hC
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_circleMap_zero,
        abs_one, one_mul]
      exact hp
    · push_neg at hp
      rw [moll_eq_zero_of_half_lt_norm ha hp]
      simp
  have hswap := integral_integral_swap hInt
  try beta_reduce at hswap
  have hz : ∀ z : V n, ∫ θ in Set.Ioc 0 (2 * Real.pi), (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z)
      = (moll n a z : ℂ) * (2 * Real.pi * h x) := by
    intro z
    rw [integral_const_mul]
    by_cases hz : ‖z‖ ≤ a / 2
    · rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_circleMap_smul_eq_two_pi_mul hh (by linarith)]
    · push_neg at hz
      rw [moll_eq_zero_of_half_lt_norm ha hz]
      simp
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le,
    show (fun θ : ℝ => ∫ z, (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z))
      = fun _ => ∫ z, (moll n a z : ℂ) * h (x + z) from funext hB,
    intervalIntegral.integral_const,
    show (fun z : V n => ∫ θ in Set.Ioc 0 (2 * Real.pi), (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z))
      = fun z => (moll n a z : ℂ) * (2 * Real.pi * h x) from funext hz,
    integral_mul_const, integral_complex_ofReal, moll_integral n ha, sub_zero,
    Complex.real_smul] at hswap
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  apply mul_left_cancel₀ h2pi
  push_cast at hswap ⊢
  linear_combination hswap

theorem holo_eq_mollify {n : ℕ} {f : V n → ℂ} {x : V n} {t : ℝ} (ht : 0 < t)
    (hf : DifferentiableOn ℂ f (closedBall x t)) : mollify n t f x = f x := by
  exact integral_moll_mul_eq_of_differentiableOn_ball ht (hf.mono ball_subset_closedBall)

end ReciprocityTheory.L2DbarEstimates.C
end

