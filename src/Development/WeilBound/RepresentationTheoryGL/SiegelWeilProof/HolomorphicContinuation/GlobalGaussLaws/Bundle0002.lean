module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussScalar
section
noncomputable section

open Complex MeasureTheory

namespace PositivityTheory.Rg.Sw.Glob.VacS

theorem gauss_scalar (b : ℂ) (hb : 0 < b.re) (s : ℝ) (w : ℂ) :
    ∫ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) =
      ((Real.pi : ℂ) / b) * cexp (-((s : ℂ) ^ 2) * ((‖w‖ ^ 2 : ℝ) : ℂ) / b) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb (I * ((2 * s : ℝ) : ℂ)) w
  have hf : (Module.finrank ℝ ℂ : ℂ) / 2 = 1 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hf, cpow_one] at h
  have e1 : ∀ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) =
      cexp (-b * (‖y‖ : ℂ) ^ 2 + I * ((2 * s : ℝ) : ℂ) * ((inner ℝ w y : ℝ) : ℂ)) := by
    intro y
    rw [← Complex.exp_add, Complex.inner, mul_comm (starRingEnd ℂ w) y]
    push_cast
    ring_nf
  simp_rw [e1]
  rw [h]
  congr 1
  congr 1
  push_cast
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0] at hb; simp at hb
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

def DG {m n : ℕ} (K : ℂ) (γ : Fin m → Fin n → ℂ) (v : Fin m → Fin n → ℂ) : ℂ :=
  K * ∏ a, ∏ j, cexp (-γ a j * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

def ftG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ))

theorem ftG_DG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (hγ : ∀ a j, 0 < (γ a j).re)
    (u : Fin m → Fin n → ℂ) :
    ftG σ s (DG K γ) u = DG (K * ∏ a, ∏ j, ((Real.pi : ℂ) / γ a j))
      (fun a j => (s : ℂ) ^ 2 * ((σ a : ℂ) ^ 2) / γ a j) u := by
  have hk : ∀ y : Fin m → Fin n → ℂ, DG K γ y *
      cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
      K * ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) := by
    intro y
    unfold DG
    have e : cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
        ∏ a, ∏ j, cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ)) := by
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 2
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
      all_goals (push_cast; try ring)
    rw [e, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  unfold ftG
  simp_rw [hk]
  rw [integral_const_mul]
  have hI : ∫ y : Fin m → Fin n → ℂ, ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) =
      ∏ a, ∏ j, (((Real.pi : ℂ) / γ a j) * cexp (-((s : ℂ) ^ 2) * ((‖(σ a : ℂ) * u a j‖ ^ 2 : ℝ) : ℂ) / γ a j)) := by
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (x : Fin n → ℂ) => ∏ j, (cexp (-γ a j * ((‖x j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * x j).re : ℂ))))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun j (z : ℂ) => (cexp (-γ a j * ((‖z‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * z).re : ℂ))))]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact gauss_scalar _ (hγ a j) s _
  rw [hI]
  unfold DG
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  congr 1
  rw [norm_mul, Complex.norm_real]
  push_cast
  have hg : γ a j ≠ 0 := by
    intro h0; have := hγ a j; rw [h0] at this; simp at this
  field_simp
  rw [Real.norm_eq_abs]
  have hs : ((|σ a| : ℝ) : ℂ) ^ 2 = ((σ a : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  push_cast
  rw [hs]
  ring

end PositivityTheory.Rg.Sw.Glob.VacS
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositivityTheory.Rg.Sw.Glob.LocCellT

variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [IsTopologicalAddGroup X]

theorem tauFact_nonneg (μ : Measure X) [μ.IsAddRightInvariant] (π : X → (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) → X) (hπs : ∀ x u, π (x + s u) = π x + u) (g : X → ℝ≥0) (hgm : Measurable g)
    (hg : ∀ x u, g (x + s u) = g x) (ρ : (Fin m → Fin n → ℂ) → ℝ) (hρ : Continuous ρ) (hρpos : ∀ u, 0 < ρ u)
    (hint : ∫⁻ z, ENNReal.ofReal (ρ (π z)) * g z ∂μ < ∞) :
    ∃ c : ℝ≥0, ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a →
      ∫ z, a (π z) * (g z : ℂ) ∂μ = (c : ℂ) * ∫ u, a u := by
  have hπm : Measurable π := hπ.measurable
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity fun z => (g z : ℝ≥0∞)).map π with hν
  have hlin : ∀ F : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable F → ∫⁻ u, F u ∂ν = ∫⁻ z, (g z : ℝ≥0∞) * F (π z) ∂μ := by
    intro F hF
    rw [hν, lintegral_map hF hπm]
    change ∫⁻ a, (F ∘ π) a ∂(μ.withDensity fun z => (g z : ℝ≥0∞)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hgm.coe_nnreal_ennreal (hF.comp hπm)]
    rfl
  have hshift : ∀ (F : (Fin m → Fin n → ℂ) → ℝ≥0∞), Measurable F → ∀ u,
      ∫⁻ z, (g z : ℝ≥0∞) * F (π z + u) ∂μ = ∫⁻ z, (g z : ℝ≥0∞) * F (π z) ∂μ := by
    intro F hF u
    have h := lintegral_add_right_eq_self (μ := μ) (fun z => (g z : ℝ≥0∞) * F (π z)) (s u)
    simpa only [hπs, hg] using h
  have : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hlin _ (measurable_one.indicator (measurable_const_add u hA)),
      hlin _ (measurable_one.indicator hA)]
    have e : ∀ z, ((fun v => u + v) ⁻¹' A).indicator (1 : (Fin m → Fin n → ℂ) → ℝ≥0∞) (π z) =
        A.indicator 1 (π z + u) := by
      intro z
      by_cases h : π z + u ∈ A
      · have h' : u + π z ∈ A := by rwa [add_comm]
        simp [Set.indicator, h, h']
      · have h' : u + π z ∉ A := by rwa [add_comm]
        simp [Set.indicator, h, h']
    simp_rw [e]
    exact hshift _ (measurable_one.indicator hA) u
  have : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨u0, hu0, hmin⟩ := hK.exists_isMinOn hne hρ.continuousOn
    have hr : 0 < ρ u0 := hρpos u0
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [← lintegral_indicator_one hKm, hlin _ (measurable_one.indicator hKm)]
    calc ∫⁻ z, (g z : ℝ≥0∞) * K.indicator 1 (π z) ∂μ
        ≤ ∫⁻ z, (ENNReal.ofReal (ρ u0))⁻¹ * (ENNReal.ofReal (ρ (π z)) * g z) ∂μ := by
          refine lintegral_mono fun z => ?_
          by_cases hz : π z ∈ K
          · have h0 : ENNReal.ofReal (ρ u0) ≠ 0 := by simp [hr]
            have h1 : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z)) :=
              calc (1 : ℝ≥0∞) = (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ u0) :=
                    (ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top).symm
                _ ≤ (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z)) :=
                    by gcongr; exact hmin hz
            calc (g z : ℝ≥0∞) * K.indicator 1 (π z) = (g z : ℝ≥0∞) * 1 := by
                  rw [Set.indicator_of_mem hz, Pi.one_apply]
              _ ≤ (g z : ℝ≥0∞) * ((ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z))) := by gcongr
              _ = (ENNReal.ofReal (ρ u0))⁻¹ * (ENNReal.ofReal (ρ (π z)) * g z) := by ring
          · simp [Set.indicator_of_notMem hz]
      _ = (ENNReal.ofReal (ρ u0))⁻¹ * ∫⁻ z, ENNReal.ofReal (ρ (π z)) * g z ∂μ := by
          rw [lintegral_const_mul']
          simp [hr]
      _ < ∞ := ENNReal.mul_lt_top (by simp [hr]) hint
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν = c • (volume : Measure (Fin m → Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  refine ⟨c, fun a ha => ?_⟩
  have h1 : ∫ u, a u ∂ν = ∫ z, a (π z) * (g z : ℂ) ∂μ := by
    rw [hν, integral_map hπm.aemeasurable ha.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hgm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [NNReal.smul_def, Complex.real_smul, mul_comm]
  rw [← h1, hc, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, Complex.real_smul]

theorem tauFact (μ : Measure X) [μ.IsAddRightInvariant] (π : X → (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) → X) (hπs : ∀ x u, π (x + s u) = π x + u) (B : X → ℂ) (hBm : Measurable B)
    (hB : ∀ x u, B (x + s u) = B x) (ρ : (Fin m → Fin n → ℂ) → ℝ) (hρ : Continuous ρ) (hρpos : ∀ u, 0 < ρ u)
    (hint : Integrable (fun z => ρ (π z) * ‖B z‖) μ) :
    ∃ κ : ℂ, ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * ρ u) →
      ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u := by
  have hπm : Measurable π := hπ.measurable
  let gs : Fin 4 → X → ℝ≥0 := ![fun z => Real.toNNReal (B z).re, fun z => Real.toNNReal (-(B z).re),
    fun z => Real.toNNReal (B z).im, fun z => Real.toNNReal (-(B z).im)]
  have hgm : ∀ j, Measurable (gs j) := by
    intro j
    fin_cases j
    exacts [(Complex.measurable_re.comp hBm).real_toNNReal, (Complex.measurable_re.comp hBm).neg.real_toNNReal,
      (Complex.measurable_im.comp hBm).real_toNNReal, (Complex.measurable_im.comp hBm).neg.real_toNNReal]
  have hgi : ∀ j x u, gs j (x + s u) = gs j x := by
    intro j x u
    fin_cases j <;> simp [gs, hB]
  have hgle : ∀ j z, ((gs j z : ℝ≥0) : ℝ) ≤ ‖B z‖ := by
    intro j z
    have h1 := Complex.abs_re_le_norm (B z)
    have h2 := Complex.abs_im_le_norm (B z)
    fin_cases j <;> simp only [gs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Real.coe_toNNReal', Fin.mk_one, Fin.reduceFinMk] <;>
      first
      | exact max_le (le_trans (le_abs_self _) h1) (norm_nonneg _)
      | exact max_le (le_trans (neg_le_abs _) h1) (norm_nonneg _)
      | exact max_le (le_trans (le_abs_self _) h2) (norm_nonneg _)
      | exact max_le (le_trans (neg_le_abs _) h2) (norm_nonneg _)
  have hfin : ∀ j, ∫⁻ z, ENNReal.ofReal (ρ (π z)) * gs j z ∂μ < ∞ := by
    intro j
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hint.lintegral_lt_top
    rw [show ((gs j z : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (gs j z) from (ENNReal.ofReal_coe_nnreal).symm,
      ← ENNReal.ofReal_mul (hρpos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hgle j z) (hρpos _).le)
  choose c hc using fun j => tauFact_nonneg μ π hπ s hπs (gs j) (hgm j) (hgi j) ρ hρ hρpos (hfin j)
  have hdec : ∀ z, B z = ((gs 0 z : ℝ) : ℂ) - ((gs 1 z : ℝ) : ℂ) + Complex.I * (((gs 2 z : ℝ) : ℂ) - ((gs 3 z : ℝ) : ℂ)) := by
    intro z
    apply Complex.ext <;> simp [gs, Real.coe_toNNReal', max_def] <;> split_ifs <;> linarith
  refine ⟨(c 0 : ℂ) - c 1 + Complex.I * ((c 2 : ℂ) - c 3), fun a ha ⟨C, hC⟩ => ?_⟩
  have hint' : ∀ j, Integrable (fun z => a (π z) * ((gs j z : ℝ≥0) : ℂ)) μ := by
    intro j
    refine Integrable.mono' (hint.const_mul C) ((ha.comp hπm).mul (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have hC0 : 0 ≤ C := by
      by_contra h
      have := hC (π z)
      nlinarith [norm_nonneg (a (π z)), hρpos (π z)]
    rw [norm_mul]
    calc ‖a (π z)‖ * ‖((gs j z : ℝ≥0) : ℂ)‖ ≤ (C * ρ (π z)) * ‖B z‖ := by
          refine mul_le_mul (hC _) ?_ (norm_nonneg _) (mul_nonneg hC0 (hρpos _).le)
          rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
          exact hgle j z
      _ = C * (ρ (π z) * ‖B z‖) := by ring
  have e : (fun z => a (π z) * B z) = fun z => (a (π z) * ((gs 0 z : ℝ≥0) : ℂ) - a (π z) * ((gs 1 z : ℝ≥0) : ℂ)) +
      Complex.I * (a (π z) * ((gs 2 z : ℝ≥0) : ℂ) - a (π z) * ((gs 3 z : ℝ≥0) : ℂ)) := by
    funext z
    rw [hdec z]
    ring
  have i01 : Integrable (fun z => a (π z) * ((gs 0 z : ℝ≥0) : ℂ) - a (π z) * ((gs 1 z : ℝ≥0) : ℂ)) μ :=
    (hint' 0).sub (hint' 1)
  have i23 : Integrable (fun z => Complex.I * (a (π z) * ((gs 2 z : ℝ≥0) : ℂ) - a (π z) * ((gs 3 z : ℝ≥0) : ℂ))) μ :=
    ((hint' 2).sub (hint' 3)).const_mul Complex.I
  rw [e, integral_add i01 i23, integral_const_mul, integral_sub (hint' 0) (hint' 1), integral_sub (hint' 2) (hint' 3)]
  have k : ∀ j, ∫ z, a (π z) * ((gs j z : ℝ≥0) : ℂ) ∂μ = (c j : ℂ) * ∫ u, a u := by
    intro j
    have := hc j a ha
    simpa using this
  rw [k 0, k 1, k 2, k 3]
  ring

end PositivityTheory.Rg.Sw.Glob.LocCellT
end
end

