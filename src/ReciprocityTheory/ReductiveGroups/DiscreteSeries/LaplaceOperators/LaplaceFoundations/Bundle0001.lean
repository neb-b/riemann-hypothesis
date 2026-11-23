module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Laplace

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.B3b
section
noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem b3b : DerivMatrixCoeffExp := by
  intro n ε H _ _ σ w hσ hw Z hZ s
  have h0 := (isDerivedOn_smE hσ).deriv Z hZ ⟨w, hw⟩
  have hphi : phiW ε σ w Z = ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    simp only [phiW, dif_pos hw]
  set g := σ (NormedSpace.exp ((s : ℂ) • Z)) with hg
  set T : H →L[ℂ] ℂ := (innerSL ℂ w).comp g with hT
  have h1 := ((T.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h0
  have h2 : HasDerivAt (fun x : ℝ => T (σ (NormedSpace.exp (((x - s : ℝ) : ℂ) • Z)) w))
      (T ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) s := by
    have h1' : HasDerivAt (⇑(ContinuousLinearMap.restrictScalars ℝ T) ∘
        fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • Z))) w)
        ((ContinuousLinearMap.restrictScalars ℝ T) ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) (s - s) := by
      rw [sub_self]; exact h1
    exact h1'.comp_sub_const s s
  rw [hphi]
  convert (preTransparency := .reducible) h2 using 1
  · funext x
    have he : NormedSpace.exp ((x : ℂ) • Z) =
        NormedSpace.exp ((s : ℂ) • Z) * NormedSpace.exp (((x - s : ℝ) : ℂ) • Z) := by
      rw [← exp_add_smul]
      congr 2
      push_cast
      ring
    rw [he, hσ.1.2 _ (exp_smul_mem_UJset hZ s) _ (exp_smul_mem_UJset hZ (x - s))]
    simp [hT, hg]
  · simp [hT, hg]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.B6
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

private theorem integrable_one_add_mul_norm_sq_rpow_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] {a s : ℝ} (ha : 0 < a) (hs : (Module.finrank ℝ E : ℝ) < 2 * s) :
    MeasureTheory.Integrable (fun v : E => (1 + a * ‖v‖ ^ 2) ^ (-s)) μ := by
  open MeasureTheory Filter Topology in
  have h := (integrable_rpow_neg_one_add_norm_sq (μ := μ) hs).comp_smul (Real.sqrt_pos.2 ha).ne'
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 ha), mul_pow,
    Real.sq_sqrt ha.le]
  congr 1
  ring

private theorem main_lemma_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] (f : ℕ → E → ℂ)
    (hm : ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.AEStronglyMeasurable (f t) μ) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hlim : ∀ v, Filter.Tendsto (fun t : ℕ => f t ((Real.sqrt t)⁻¹ • v)) Filter.atTop
      (nhds (Complex.exp (-(B v v)))))
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hbd : ∀ᶠ t : ℕ in Filter.atTop, ∀ v, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.Integrable (f t) μ ∧ ∫ v, f t v ∂μ ≠ 0 := by
  open MeasureTheory Filter Topology in
  have hbig : ∀ᶠ t : ℕ in atTop, (Module.finrank ℝ E : ℝ) < 2 * (γ * t) ∧ (1 : ℝ) ≤ t := by
    have h1 : Tendsto (fun t : ℕ => 2 * (γ * (t : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop two_pos (Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop)
    filter_upwards [h1.eventually_gt_atTop (Module.finrank ℝ E : ℝ), eventually_ge_atTop 1]
      with t ht ht1
    exact ⟨ht, by exact_mod_cast ht1⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hbd.and hm).and hbig)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (hN N le_rfl).2.2

  have hmaj : ∀ t : ℕ, N ≤ t → ∀ w : E,
      ‖f t ((Real.sqrt t)⁻¹ • w)‖ ≤ (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N)) := by
    intro t ht w
    have ht' : (N : ℝ) ≤ t := by exact_mod_cast ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos ht'
    have h1 := (hN t ht).1.1 ((Real.sqrt t)⁻¹ • w)
    have hn : ‖(Real.sqrt t)⁻¹ • w‖ ^ 2 = ‖w‖ ^ 2 / t := by
      rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt htpos.le]
      ring
    rw [hn] at h1
    refine h1.trans ?_
    have hx : 0 ≤ c * ‖w‖ ^ 2 := by positivity
    have hmono := ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.mono_pow hx hNpos ht'
    have hA : 0 < 1 + c * ‖w‖ ^ 2 / N := by positivity
    have hB : 0 < 1 + c * ‖w‖ ^ 2 / t := by positivity
    have key : (1 + c * ‖w‖ ^ 2 / N) ^ (γ * N) ≤ (1 + c * ‖w‖ ^ 2 / t) ^ (γ * t) := by
      rw [mul_comm γ (N : ℝ), mul_comm γ (t : ℝ), Real.rpow_mul hA.le, Real.rpow_mul hB.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hmono hγ.le
    have e1 : c * (‖w‖ ^ 2 / t) = c * ‖w‖ ^ 2 / t := by ring
    have e2 : c / N * ‖w‖ ^ 2 = c * ‖w‖ ^ 2 / N := by ring
    rw [e1, e2, Real.rpow_neg hB.le, Real.rpow_neg hA.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hA _) key
  have hbint : Integrable (fun w : E => (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N))) μ :=
    integrable_one_add_mul_norm_sq_rpow_neg μ (div_pos hc hNpos) (hN N le_rfl).2.1
  have hgm : ∀ t : ℕ, N ≤ t → AEStronglyMeasurable (fun w => f t ((Real.sqrt t)⁻¹ • w)) μ := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos (by exact_mod_cast ht)
    have hr : (Real.sqrt t)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 htpos).ne'
    exact (hN t ht).1.2.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul μ hr)
  have hT : Tendsto (fun t : ℕ => ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ) atTop
      (𝓝 (∫ w, Complex.exp (-(B w w)) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence _
      ((eventually_ge_atTop N).mono hgm)
      ((eventually_ge_atTop N).mono fun t ht => Eventually.of_forall (hmaj t ht))
      hbint (Eventually.of_forall hlim)

  have hpos : ∀ v : E, v ≠ 0 → 0 < (B v v).re := by
    intro v hv
    have hle : ‖Complex.exp (-(B v v))‖ ≤ (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) :=
      le_of_tendsto (hlim v).norm (eventually_atTop.2 ⟨N, fun t ht => hmaj t ht v⟩)
    have hlt : (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · have hv' := norm_pos_iff.2 hv
        have : 0 < c / N * ‖v‖ ^ 2 := by positivity
        linarith
      · have := mul_pos hγ hNpos
        linarith
    rw [Complex.norm_exp] at hle
    have h3 : Real.exp (-(B v v)).re < 1 := hle.trans_lt hlt
    have h4 := Real.exp_lt_exp.1 (h3.trans_eq Real.exp_zero.symm)
    rw [Complex.neg_re] at h4
    linarith
  have hev : ∀ᶠ t : ℕ in atTop, ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ ≠ 0 :=
    hT.eventually_ne (ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero μ B hpos)
  filter_upwards [eventually_ge_atTop N, hev] with t ht hgt
  refine ⟨?_, ?_⟩
  · exact Integrable.mono' (integrable_one_add_mul_norm_sq_rpow_neg μ hc (hN t ht).2.1) (hN t ht).1.2
      (Eventually.of_forall (hN t ht).1.1)
  · intro h0
    apply hgt
    rw [Measure.integral_comp_smul μ (f t) (Real.sqrt t)⁻¹, h0, smul_zero]

theorem b6 : GaussianLimitHaar := by
  intro E _ _ _ _ _ μ _ f hm B hlim c γ hc hγ hbd
  exact main_lemma_2 μ f hm B hlim hc hγ hbd

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.DoubleSumDiagSplit
section
noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem double_sum_diag_split {n : ℕ} (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ a, ∑ b, (if a < b then f a b + f b a else 0) := by
  have h1 : ∀ a b, f a b = (if a < b then f a b else 0) + (if a = b then f a b else 0)
      + (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have h2 : ∑ a, ∑ b, (if b < a then f a b else 0) = ∑ a, ∑ b, (if a < b then f b a else 0) :=
    Finset.sum_comm
  calc ∑ a, ∑ b, f a b
      = ∑ a, ∑ b, ((if a < b then f a b else 0) + (if a = b then f a b else 0)
          + (if b < a then f a b else 0)) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))
    _ = ∑ a, ∑ b, (if a < b then f a b else 0) + ∑ a, f a a
          + ∑ a, ∑ b, (if b < a then f a b else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        rw [h2, add_comm (∑ a, ∑ b, (if a < b then f a b else 0)) (∑ a, f a a), add_assoc,
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        split_ifs <;> simp

theorem b2Id : RaisingLoweringNormIdentities := by
  intro n ε M _ _ E lam w hD
  obtain ⟨hGl, hU, hw1, ⟨hdiag, hup⟩, hcas⟩ := hD
  set Λ := lowK ε lam with hΛ
  let sR : Fin n → Fin n → ℝ := fun a b => if ε a = ε b then 1 else -1
  have hsC : ∀ a b, adjSign ε a b = ((sR a b : ℝ) : ℂ) := by
    intro a b; simp only [adjSign, sR]; split_ifs <;> simp
  have hsymm : ∀ a b, sR a b = sR b a := by
    intro a b; simp only [sR]
    by_cases h : ε a = ε b
    · simp [h]
    · simp [h, Ne.symm h]
  have hsq : ∀ a b, sR a b * sR a b = 1 := by
    intro a b; simp only [sR]; split_ifs <;> norm_num
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hQ : ∀ a b, ⟪w, E a b (E b a w)⟫_ℂ = ((sR a b * ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    have h := hU b a w (E b a w)
    rw [inner_self_eq_norm_sq_to_K, hsC] at h
    have h1 : ((sR b a : ℝ) : ℂ) * ((sR b a : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq]; simp
    calc ⟪w, E a b (E b a w)⟫_ℂ
        = ((sR b a : ℝ) : ℂ) * (((sR b a : ℝ) : ℂ) * ⟪w, E a b (E b a w)⟫_ℂ) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [← h, hsymm b a]; try simp only [RCLike.ofReal_eq_complex_ofReal]
          push_cast; ring
  have hC : ∀ a b, ⟪w, E a b (E b a w)⟫_ℂ - ⟪w, E b a (E a b w)⟫_ℂ = (((Λ a - Λ b : ℝ)) : ℂ) := by
    intro a b
    have h := hGl a b b a
    rw [if_pos rfl, if_pos rfl] at h
    have h2 := congrArg (fun T : Module.End ℂ M => T w) h
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
    rw [← inner_sub_right, h2, hdiag a, hdiag b, ← sub_smul, inner_smul_right, hww, mul_one]
    push_cast; ring
  have hR1 : ∀ a b, sR a b * ‖E b a w‖ ^ 2 - sR b a * ‖E a b w‖ ^ 2 = Λ a - Λ b := by
    intro a b
    have h := hC a b
    rw [hQ a b, hQ b a, ← Complex.ofReal_sub] at h
    exact_mod_cast h
  have hR2 : ∀ a, ‖E a a w‖ ^ 2 = Λ a ^ 2 := by
    intro a
    rw [hdiag a, norm_smul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hR3 : ∀ a b, a < b → ε a = ε b → ‖E a b w‖ ^ 2 = 0 := by
    intro a b hab he; rw [hup a b hab he]; simp
  have hcasR : casVal lam = ∑ a, ∑ b, sR a b * ‖E b a w‖ ^ 2 := by
    have h1 : ⟪w, casimir E w⟫_ℂ = ∑ a, ∑ b, ⟪w, E a b (E b a w)⟫_ℂ := by
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
    rw [hcas, inner_smul_right, hww, mul_one] at h1
    simp only [hQ] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab he
    have h := hR1 a b
    have hs1 : sR a b = 1 := if_pos he
    have hs2 : sR b a = 1 := if_pos he.symm
    rw [hs1, hs2, hR3 a b hab he] at h
    linarith
  · intro a b hab he
    have h := hR1 a b
    have hs1 : sR a b = -1 := if_neg he
    have hs2 : sR b a = -1 := if_neg (Ne.symm he)
    rw [hs1, hs2] at h
    linarith
  · have hpt : ∀ a b, (if a < b then sR a b * ‖E b a w‖ ^ 2 + sR b a * ‖E a b w‖ ^ 2 else 0) =
        (if a < b ∧ ε b = ε a then Λ a else 0) - (if a < b ∧ ε a = ε b then Λ b else 0)
        - ((if a < b ∧ ε b ≠ ε a then Λ a else 0) - (if a < b ∧ ε a ≠ ε b then Λ b else 0))
        - 2 * (if a < b ∧ ε a ≠ ε b then ‖E b a w‖ ^ 2 else 0) := by
      intro a b
      by_cases hab : a < b
      · have h := hR1 a b
        by_cases he : ε a = ε b
        · have hs1 : sR a b = 1 := if_pos he
          have hs2 : sR b a = 1 := if_pos he.symm
          have h0 := hR3 a b hab he
          rw [hs1, hs2, h0] at h
          simp [hab, he, hs1, hs2, h0]
          linarith
        · have hs1 : sR a b = -1 := if_neg he
          have hs2 : sR b a = -1 := if_neg (Ne.symm he)
          rw [hs1, hs2] at h
          simp [hab, he, Ne.symm he, hs1, hs2]
          linarith
      · simp [hab]
    have hsw1 : ∑ a, ∑ b, (if b < a ∧ ε b = ε a then Λ a else 0) =
        ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0) := Finset.sum_comm
    have hsw2 : ∑ a, ∑ b, (if b < a ∧ ε b ≠ ε a then Λ a else 0) =
        ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0) := Finset.sum_comm
    have hA : 2 * ∑ a, Λ a * rhoC ε a = ∑ a, ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0) := by
      rw [← hsw1, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0) =
          Λ a * ∑ b, (if a < b ∧ ε b = ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      have e2 : ∑ b, (if b < a ∧ ε b = ε a then Λ a else 0) =
          Λ a * ∑ b, (if b < a ∧ ε b = ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [e1, e2]
      simp only [rhoC, Finset.natCast_card_filter]
      ring
    have hB : 2 * ∑ a, Λ a * rhoN ε a = ∑ a, ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0) := by
      rw [← hsw2, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0) =
          Λ a * ∑ b, (if a < b ∧ ε b ≠ ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      have e2 : ∑ b, (if b < a ∧ ε b ≠ ε a then Λ a else 0) =
          Λ a * ∑ b, (if b < a ∧ ε b ≠ ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [e1, e2]
      simp only [rhoN, Finset.natCast_card_filter]
      ring
    have hdiagsum : ∑ a, sR a a * ‖E a a w‖ ^ 2 = ∑ a, Λ a ^ 2 :=
      Finset.sum_congr rfl (fun a _ => by rw [hR2 a, show sR a a = 1 from if_pos rfl, one_mul])
    have hspl := double_sum_diag_split (fun a b => sR a b * ‖E b a w‖ ^ 2)
    have hcasv : casVal lam = ∑ a, Λ a ^ 2 + (∑ a, ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0)
        - (∑ a, ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0)
          - ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0))
        - 2 * ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then ‖E b a w‖ ^ 2 else 0)) := by
      rw [hcasR, hspl, hdiagsum]
      congr 1
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hz : ∑ a, (Λ a ^ 2 + 2 * (Λ a * rhoC ε a) - 2 * (Λ a * rhoN ε a) - lam a * lam a
        + (rhoN ε - rhoC ε) a * (rhoN ε - rhoC ε) a) = 0 :=
      Finset.sum_eq_zero (fun a _ => by simp only [hΛ, lowK, Pi.add_apply, Pi.sub_apply]; ring)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hz
    simp only [Finset.sum_filter]
    simp only [casVal, nsq, dot] at hcasv ⊢
    linarith [hcasv, hz, hA, hB]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.MeasurableEmbeddingLeftMulOfIsUnit
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

variable {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem measurableEmbedding_leftMul_of_isUnit {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : IsUnit g) :
    MeasurableEmbedding (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) g) := by
  obtain ⟨u, rfl⟩ := hg
  let e : Formalism.QuantumDeterminants.Mt k r ≃ₜ Formalism.QuantumDeterminants.Mt k r :=
    { toFun := Formalism.QuantumDeterminants.lmulM (u : Matrix _ _ ℂ)
      invFun := Formalism.QuantumDeterminants.lmulM ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ)
      left_inv := fun x => by
        change ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * ((u : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by
        change (u : Matrix _ _ ℂ) * (((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      continuous_toFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      continuous_invFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id }
  exact e.toMeasurableEquiv.measurableEmbedding

theorem adjoint_comp_self_of_isometry (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) :
    (ContinuousLinearMap.adjoint A).comp A = 1 := by
  let L : V →ₗᵢ[ℂ] V := { toLinearMap := (A : V →ₗ[ℂ] V), norm_map' := hA }
  ext v
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact L.inner_map_map y v

theorem opNorm_le_one_of_isometry_alt (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hA, one_mul]

theorem schur_orthogonality_unitary_rep (G : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [IsProbabilityMeasure μ]
    (hG0 : μ {x | Matrix.of x ∉ G} = 0) (hGu : ∀ g ∈ G, IsUnit g)
    (hinv : ∀ g ∈ G, μ.map (Formalism.QuantumDeterminants.lmulM g) = μ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V))
    (hmul : ∀ g ∈ G, ∀ h ∈ G, σ (g * h) = σ g * σ h) (hunit : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V, (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => σ (Matrix.of x)) μ) [Nontrivial V]
    (u u' v v' : V) :
    ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ =
      ⟪v', v⟫_ℂ * ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
  classical
  set A : V →L[ℂ] V := (innerSL ℂ u').smulRight u with hA
  set F : Formalism.QuantumDeterminants.Mt k r → (V →L[ℂ] V) := fun x =>
    (σ (Matrix.of x)).comp (A.comp (ContinuousLinearMap.adjoint (σ (Matrix.of x)))) with hF
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ G := by
    rw [ae_iff]; simpa using hG0
  have hFm : AEStronglyMeasurable F μ := by
    have hc : Continuous (fun S : V →L[ℂ] V => S.comp (A.comp (ContinuousLinearMap.adjoint S))) :=
      continuous_id.clm_comp (continuous_const.clm_comp
        (ContinuousLinearMap.adjoint : (V →L[ℂ] V) ≃ₗᵢ⋆[ℂ] (V →L[ℂ] V)).continuous)
    exact hc.comp_aestronglyMeasurable hmeas
  have hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖A‖ := hae.mono fun x hx => by
    have h1 := opNorm_le_one_of_isometry_alt _ (hunit _ hx)
    have h2 : ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact h1
    calc ‖F x‖ ≤ ‖σ (Matrix.of x)‖ * (‖A‖ * ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖A‖ * 1) := by gcongr
      _ = ‖A‖ := by ring
  have hFi : Integrable F μ := Integrable.of_bound hFm ‖A‖ hFb
  have hFzi : ∀ z, Integrable (fun x => F x z) μ := fun z => hFi.apply_continuousLinearMap z
  set B : V →L[ℂ] V := ∫ x, F x ∂μ with hB
  have happ : ∀ z, B z = ∫ x, F x z ∂μ := fun z => ContinuousLinearMap.integral_apply hFi z
  have hadj : ∀ g ∈ G, (ContinuousLinearMap.adjoint (σ g)).comp (σ g) = 1 :=
    fun g hg => adjoint_comp_self_of_isometry _ (hunit g hg)
  have hcomm : ∀ g ∈ G, ∀ z, σ g (B z) = B (σ g z) := by
    intro g hg z
    rw [happ, happ, ← ContinuousLinearMap.integral_comp_comm _ (hFzi z)]
    have key : ∀ᵐ x ∂μ, σ g (F x z) = F (Formalism.QuantumDeterminants.lmulM g x) (σ g z) := hae.mono fun x hx => by
      have e : Matrix.of (Formalism.QuantumDeterminants.lmulM g x) = g * Matrix.of x := rfl
      simp only [hF, e, hmul g hg _ hx]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      simp only [ContinuousLinearMap.comp_apply]
      have := congrArg (fun T : V →L[ℂ] V => T z) (hadj g hg)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
      rw [this]
    rw [integral_congr_ae key]
    conv_rhs => rw [← hinv g hg]
    rw [(measurableEmbedding_leftMul_of_isUnit (hGu g hg)).integral_map]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z, B z = c • z := by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (B : Module.End ℂ V)
    refine ⟨c, fun z => ?_⟩
    have hS : ∀ g ∈ G, ∀ v ∈ Module.End.eigenspace (B : Module.End ℂ V) c,
        σ g v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := by
      intro g hg v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      change B (σ g v) = c • σ g v
      rw [← hcomm g hg]
      change σ g ((B : Module.End ℂ V) v) = c • σ g v
      rw [hv, map_smul]
    rcases hirr _ hS with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hv1 := hv.apply_eq_smul
      have hv0 := hv.2
      have : v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := Module.End.mem_eigenspace_iff.2 hv1
      rw [h, Submodule.mem_bot] at this
      exact hv0 this
    · have : z ∈ Module.End.eigenspace (B : Module.End ℂ V) c := h ▸ Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 this
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have htr : c * (Module.finrank ℂ V : ℂ) = ⟪u', u⟫_ℂ := by
    let tr : (V →L[ℂ] V) →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ))
    have htrv : ∀ T : V →L[ℂ] V, tr T = LinearMap.trace ℂ V (T : V →ₗ[ℂ] V) := fun T => rfl
    have h1 : tr B = ∫ x, tr (F x) ∂μ := (ContinuousLinearMap.integral_comp_comm tr hFi).symm
    have h2 : ∀ᵐ x ∂μ, tr (F x) = ⟪u', u⟫_ℂ := hae.mono fun x hx => by
      rw [htrv]
      have e1 : ((F x : V →L[ℂ] V) : V →ₗ[ℂ] V) =
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) ∘ₗ
            (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) := rfl
      rw [e1, LinearMap.trace_comp_comm']
      have e2 : (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) ∘ₗ
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) = (A : V →ₗ[ℂ] V) := by
        have := hadj _ hx
        ext y
        have h3 := congrArg (fun T : V →L[ℂ] V => T (A y)) this
        simpa using h3
      rw [e2]
      have e3 : (A : V →ₗ[ℂ] V) = ((innerSL ℂ u' : V →L[ℂ] ℂ) : V →ₗ[ℂ] ℂ).smulRight u := by
        ext y; rfl
      rw [e3, LinearMap.trace_smulRight]
      rfl
    have h3 : tr B = c * (Module.finrank ℂ V : ℂ) := by
      have eB : B = c • (1 : V →L[ℂ] V) := by ext z; simp [hc z]
      rw [htrv, eB]
      simp [LinearMap.trace_one]
    rw [← h3, h1, integral_congr_ae h2, integral_const]
    simp
  have hfin : ⟪v', B v⟫_ℂ = ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ := by
    rw [happ, ← integral_inner (hFzi v)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_smul, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
    ring
  rw [← hfin, hc, inner_smul_right]
  have hc' : c = ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
    rw [← htr]; field_simp
  rw [hc']
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

