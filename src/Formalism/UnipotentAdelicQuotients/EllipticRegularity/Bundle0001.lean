module

public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009

@[expose] public section

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.BaseLevel
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma norm_fourier_le_integral_norm {d : ℕ} (g : E d → ℂ) (ξ : E d) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem sobolevOfCompactSupport : BaseLevel := by
  intro d g hg hgs
  unfold Hs nrm
  have hint : MeasureTheory.Integrable g := hg.integrable_of_hasCompactSupport hgs
  set B : ℝ := ∫ x, ‖g x‖ with hB
  have hBnn : 0 ≤ B := MeasureTheory.integral_nonneg fun x => norm_nonneg _
  have hI : MeasureTheory.Integrable
      (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    have : (Module.finrank ℝ (E d) : ℝ) = d := by simp
    rw [this]
    linarith
  have hI2 := (hI.const_mul (B ^ 2)).hasFiniteIntegral
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun ξ => ?_) hI2
  have ha : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hom : om (-(d : ℝ) - 1) 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2) := by simp [om]
  have hsq : ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have h1 : ‖𝓕 g ξ‖ₑ ≤ ENNReal.ofReal B := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (norm_fourier_le_integral_norm g ξ)
  have h2 : ‖B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)‖ₑ =
      ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]
  rw [h2, hom]
  calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ‖𝓕 g ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ENNReal.ofReal B ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hBnn,
          ← ENNReal.ofReal_mul (by positivity), hsq, mul_comm]

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.ConvolutionBound
section
namespace ZetaZeros.D.EllReg

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

private lemma conv_sq_le (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) (ξ : E d) :
    (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := by
  first | exact UpperTheory.Reformulated.B.Qj8.conv_sq_le .. | (apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg ξ | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d

private lemma conv_young (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) :
    ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η ^ 2) :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((hg.comp measurable_snd).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := lintegral_mono fun ξ => conv_sq_le k g hk hg ξ
    _ = (∫⁻ ζ, k ζ) * ∫⁻ ξ, ∫⁻ η, k (ξ - η) * g η ^ 2 :=
      lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, ∫⁻ ξ, k (ξ - η) * g η ^ 2 := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, (∫⁻ ζ, k ζ) * g η ^ 2 := by
      congr 1
      refine lintegral_congr fun η => ?_
      rw [lintegral_mul_const _ (show Measurable fun ξ => k (ξ - η) from hk.comp (measurable_id.sub measurable_const)),
        lintegral_sub_right_eq_self k η]
    _ = (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
      rw [lintegral_const_mul _ (hg.pow_const 2)]; ring

private lemma om_measurable (s M ε : ℝ) : Measurable (om (d := d) s M ε) := by
  unfold om; fun_prop

private lemma om_nonneg (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om; positivity

theorem convolution_bound : ConvBound := by
  intro d s M ε C N hC hom K F hK hF
  have hKm : Measurable K := hK.measurable
  have hFm : Measurable F := hF.measurable
  obtain ⟨k1, hk1e⟩ : ∃ k1 : E d → ℝ≥0∞, k1 = fun ζ => ‖K ζ‖ₑ := ⟨_, rfl⟩
  obtain ⟨k3, hk3e⟩ : ∃ k3 : E d → ℝ≥0∞, k3 = fun ζ => ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ :=
    ⟨_, rfl⟩
  obtain ⟨k2, hk2e⟩ : ∃ k2 : E d → ℝ≥0∞, k2 = fun ζ => ENNReal.ofReal C * k3 ζ := ⟨_, rfl⟩
  obtain ⟨g1, hg1e⟩ : ∃ g1 : E d → ℝ≥0∞, g1 = fun η => ENNReal.ofReal (om s M ε η) * ‖F η‖ₑ := ⟨_, rfl⟩
  obtain ⟨g2, hg2e⟩ : ∃ g2 : E d → ℝ≥0∞, g2 = fun η => ENNReal.ofReal (om (s - 1) M ε η) * ‖F η‖ₑ :=
    ⟨_, rfl⟩
  have hk1 : Measurable k1 := by rw [hk1e]; exact hKm.enorm
  have hk3 : Measurable k3 := by
    rw [hk3e]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hKm.enorm
  have hk2 : Measurable k2 := by rw [hk2e]; exact measurable_const.mul hk3
  have hg1 : Measurable g1 := by
    rw [hg1e]; exact (ENNReal.measurable_ofReal.comp (om_measurable s M ε)).mul hFm.enorm
  have hg2 : Measurable g2 := by
    rw [hg2e]; exact (ENNReal.measurable_ofReal.comp (om_measurable (s - 1) M ε)).mul hFm.enorm
  have hprod : ∀ k g : E d → ℝ≥0∞, Measurable k → Measurable g →
      Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η) := fun k g hk hg =>
    (hk.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)
  have hT1 : Measurable fun ξ => ∫⁻ η, k1 (ξ - η) * g1 η := (hprod k1 g1 hk1 hg1).lintegral_prod_right'
  have hT2 : Measurable fun ξ => ∫⁻ η, k2 (ξ - η) * g2 η := (hprod k2 g2 hk2 hg2).lintegral_prod_right'

  have hpt : ∀ ξ, ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ ≤
      (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := by
    intro ξ
    have h1 : ‖conv K F ξ‖ₑ ≤ ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by
      unfold conv
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun η => ?_
      rw [enorm_mul]
    have hmeas : Measurable fun η => k1 (ξ - η) * g1 η :=
      (hk1.comp (measurable_const.sub measurable_id)).mul hg1
    calc ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ
        ≤ ENNReal.ofReal (om s M ε ξ) * ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by gcongr
      _ = ∫⁻ η, ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, (k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η) := by
        refine lintegral_mono fun η => ?_
        have hr : om s M ε ξ ≤ om s M ε η + C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η := by
          have h := hom ξ η
          have h' := le_abs_self (om s M ε ξ - om s M ε η)
          linarith
        have hX : 0 ≤ ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N := by positivity
        have hY := om_nonneg (s - 1) M ε η
        have he : ENNReal.ofReal (om s M ε ξ) ≤ ENNReal.ofReal (om s M ε η) +
            ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η)) := by
          rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_add (om_nonneg s M ε η) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_le_of_eq hr (by ring))
        calc ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ)
            ≤ (ENNReal.ofReal (om s M ε η) + ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η))) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) := by gcongr
          _ = k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η := by
            rw [hk1e, hk2e, hk3e, hg1e, hg2e]; ring
      _ = (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := lintegral_add_left hmeas _
  have hn : nrm s M ε (conv K F) ≤
      ∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ) := by
    unfold nrm
    refine lintegral_mono fun ξ => ?_
    rw [ENNReal.rpow_two, ← mul_pow]
    gcongr
    exact hpt ξ
  have hY : ∀ (k g : E d → ℝ≥0∞), Measurable k → Measurable g →
      (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) := by
    intro k g hk hg
    have h := conv_young k g hk hg
    simp only [← ENNReal.rpow_two] at h ⊢
    calc (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ ((∫⁻ ζ, k ζ) ^ (2 : ℝ) * ∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num
  have e1 : ∫⁻ η, g1 η ^ 2 = nrm s M ε F := by
    unfold nrm; rw [hg1e]; simp only [mul_pow]
  have e2 : ∫⁻ η, g2 η ^ 2 = nrm (s - 1) M ε F := by
    unfold nrm; rw [hg2e]; simp only [mul_pow]
  have e3 : ∫⁻ ζ, k2 ζ = ENNReal.ofReal C * ∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ := by
    rw [hk2e, lintegral_const_mul _ hk3, hk3e]
  have e4 : ∫⁻ ζ, k1 ζ = ∫⁻ ζ, ‖K ζ‖ₑ := by rw [hk1e]
  have hMk := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2) hT1.aemeasurable hT2.aemeasurable
    (by norm_num)
  simp only [Pi.add_apply] at hMk
  calc nrm s M ε (conv K F) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hn (by norm_num)
    _ ≤ (∫⁻ ξ, (∫⁻ η, k1 (ξ - η) * g1 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        (∫⁻ ξ, (∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hMk
    _ ≤ (∫⁻ ζ, k1 ζ) * (∫⁻ η, g1 η ^ 2) ^ (1 / 2 : ℝ) + (∫⁻ ζ, k2 ζ) * (∫⁻ η, g2 η ^ 2) ^ (1 / 2 : ℝ) :=
        add_le_add (hY k1 g1 hk1 hg1) (hY k2 g2 hk2 hg2)
    _ = _ := by rw [e1, e2, e3, e4]

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.IteratedPartialFourierChar
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable def eL {d : ℕ} (ξ : E d) : E d →L[ℝ] ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))

lemma eF_eq_exp {d : ℕ} (ξ : E d) : eF ξ = fun y => Complex.exp (eL ξ y) := by
  funext y
  simp only [eF, eL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, real_inner_comm y ξ]
  ring_nf

lemma hasFDerivAt_eF {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by
  rw [eF_eq_exp]
  exact (eL ξ).hasFDerivAt.cexp

lemma eL_ev {d : ℕ} (ξ : E d) (j : Fin d) : eL ξ (ev j) = -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) := by
  simp only [eL, ev, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, EuclideanSpace.inner_single_right]
  simp

theorem iteratedPartialFourierChar : DwExp := by
  intro d ξ w
  induction w with
  | nil => funext y; simp [dw]
  | cons j w ih =>
    funext x
    have hfun : dw w (eF ξ) =
        fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y := ih
    show fderiv ℝ (dw w (eF ξ)) x (ev j) = _
    rw [hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons,
      eF_eq_exp]
    ring

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernDecay
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def derivL1Norm (f : V → ℂ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖

lemma derivL1Norm_nonneg (f : V → ℂ) (n : ℕ) : 0 ≤ derivL1Norm f n :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

lemma integrable_iteratedFDeriv {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) := by
  have hcont : Continuous (fun v => iteratedFDeriv ℝ n f v) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hc : Continuous (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    (continuous_norm.pow k).mul hcont.norm
  have hs : HasCompactSupport (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    ((hfc.iteratedFDeriv n).comp_left norm_zero).mul_left
  exact hc.integrable_of_hasCompactSupport hs

lemma pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖w‖ ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * derivL1Norm f n := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := n)
    (hf.of_le (by exact_mod_cast le_top))
    (fun k j _ _ => integrable_iteratedFDeriv hf hfc k j) (k := 0) (n := n) (by simp) le_rfl w
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
    Finset.sum_product, Finset.sum_range_one] at h
  unfold derivL1Norm
  exact h

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have htn : 0 ≤ t ^ n := pow_nonneg ht n
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n ≤ 2 ^ n * (1 + t ^ n) := le_mul_of_one_le_right h2 (by linarith)
    linarith
  · have h1 : (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n * t ^ n ≤ 2 ^ n * (1 + t ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2
    rw [mul_pow] at h1
    linarith

lemma one_add_pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (n : ℕ) (w : V) :
    (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by
  have hL := pow_mul_norm_fourier_le hf hfc n w
  have h0 := pow_mul_norm_fourier_le hf hfc 0 w
  simp only [pow_zero, one_mul] at h0
  have hmono : derivL1Norm f 0 ≤ derivL1Norm f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => integral_nonneg fun _ => norm_nonneg _)
  have hpos : 0 ≤ ‖𝓕 f w‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hb := one_add_pow_le ‖w‖ (norm_nonneg w) n
  calc (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖𝓕 f w‖ := mul_le_mul_of_nonneg_right hb hpos
    _ = 2 ^ n * (‖𝓕 f w‖ + ‖w‖ ^ n * ‖𝓕 f w‖) := by ring
    _ ≤ 2 ^ n * (derivL1Norm f n + 2 ^ n * derivL1Norm f n) := by
        refine mul_le_mul_of_nonneg_left ?_ h2
        linarith
    _ = 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by ring

lemma norm_fourier_le_rpow {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n * (1 + ‖w‖) ^ (-(n : ℝ)) := by
  have h5 := one_add_pow_mul_norm_fourier_le hf hfc n w
  have hp : 0 < 1 + ‖w‖ := by positivity
  have hpn : 0 < (1 + ‖w‖) ^ n := pow_pos hp n
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpn]
  linarith [h5, mul_comm ((1 + ‖w‖) ^ n) ‖𝓕 f w‖]

lemma lintegral_weight_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) ≤
      ENNReal.ofReal (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1))) *
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  dsimp only
  have hp : 0 < 1 + ‖w‖ := by positivity
  have h6 := norm_fourier_le_rpow hf hfc (m + (Module.finrank ℝ V + 1)) w
  have hA : 0 ≤ (1 + ‖w‖) ^ m := by positivity
  have hC : 0 ≤ 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
      derivL1Norm f (m + (Module.finrank ℝ V + 1)) :=
    mul_nonneg (by positivity) (derivL1Norm_nonneg f _)
  have hexp : (1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ)) =
      (1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  calc (1 + ‖w‖) ^ m * ‖𝓕 f w‖
      ≤ (1 + ‖w‖) ^ m * (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h6 hA
    _ = 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        ((1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hexp]

lemma lintegral_weight_fourier_lt_top {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_weight_fourier_le hf hfc m)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm ?_))
  push_cast
  linarith

end

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernDil
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma norm_fourier_comp_dil (c : V → ℂ) (r : ℝ) (hr : 0 < r) (x0 w : V) :
    ‖𝓕 (fun x => c (r⁻¹ • (x - x0))) w‖ = r ^ Module.finrank ℝ V * ‖𝓕 c (r • w)‖ := by
  have hrw : ∀ y : V, Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y =
      Complex.exp (↑(-2 * Real.pi * inner ℝ x0 w) * Complex.I) *
        (Complex.exp (↑(-2 * Real.pi * inner ℝ y (r • w)) * Complex.I) • c y) := by
    intro y
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    push_cast
    ring
  rw [Real.fourier_eq', Real.fourier_eq']
  have h1 : (∫ v : V, Complex.exp (↑(-2 * Real.pi * inner ℝ v w) * Complex.I) • c (r⁻¹ • (v - x0))) =
      ∫ v : V, (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y)
        (r⁻¹ • v) := by
    rw [← MeasureTheory.integral_add_right_eq_self _ x0]
    congr 1
    funext v
    simp only [add_sub_cancel_right, smul_inv_smul₀ hr.ne']
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (MeasureTheory.volume : MeasureTheory.Measure V)
    (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y) hr.le
  rw [h1.trans h2]
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul, norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma lintegral_dil_weight (r : ℝ) (hr : 0 < r) (D : ℝ) (hD : (Module.finrank ℝ V : ℝ) < D) :
    (∫⁻ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D))) =
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-D)) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hmeas : Measurable (fun w : V => r • w) := measurable_const_smul r
  have hg : Measurable (fun u : V => ENNReal.ofReal ((1 + ‖u‖) ^ (-D))) := by fun_prop
  have h1 : ∀ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D)) =
      ENNReal.ofReal (r ^ Module.finrank ℝ V) * ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D)) :=
    fun w => ENNReal.ofReal_mul (by positivity)
  simp_rw [h1]
  have hg' : Measurable (fun w : V => ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D))) := hg.comp hmeas
  rw [MeasureTheory.lintegral_const_mul _ hg']
  rw [← MeasureTheory.lintegral_map hg hmeas, MeasureTheory.Measure.map_addHaar_smul _ hr0,
    MeasureTheory.lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

end

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.PairingLocal
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma dw_eventuallyEq {d : ℕ} (w : List (Fin d)) {f f' : E d → ℂ} {y : E d} (h : f =ᶠ[𝓝 y] f') :
    dw w f =ᶠ[𝓝 y] dw w f' := by
  induction w with
  | nil => simpa [dw] using h
  | cons j w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with x hx
    show fderiv ℝ (dw w f) x (ev j) = fderiv ℝ (dw w f') x (ev j)
    rw [hx]

theorem adjointPairingLocal : PairingLocal := by
  intro d m b b' g φ V hV hg hb
  congr 1
  funext y
  by_cases hy : y ∈ V
  · congr 1
    unfold trOp
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
    congr 1

    have hev : (fun y => b n w y * φ y) =ᶠ[𝓝 y] (fun y => b' n w y * φ y) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [hb n w z hz]
    exact (dw_eventuallyEq _ hev).eq_of_nhds
  · have hg0 : g y = 0 := by
      first
        | exact image_eq_zero_of_nmem_tsupport (fun h => hy (hg h))
        | exact image_eq_zero_of_notMem_tsupport (fun h => hy (hg h))
    rw [hg0, zero_mul, zero_mul]

end ZetaZeros.D.EllReg
end

