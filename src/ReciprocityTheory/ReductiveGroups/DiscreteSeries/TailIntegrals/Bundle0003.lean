module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PolynomialGrowthIntegrals
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace subgroupData

def qv (c : Fin 3 → ℂ) (t : ℝ) : ℂ := c 0 + c 1 * t + c 2 * t ^ 2

lemma qv_cont (c : Fin 3 → ℂ) : Continuous (qv c) := by
  unfold qv; fun_prop

lemma term_bd {z : ℂ} {w d la W D : ℝ} (hz : ‖z‖ ≤ la) (hw : |w| ≤ W) (hD : 0 < D) (hd : D ≤ |d|) :
    ‖z * (w : ℂ) / (d : ℂ)‖ ≤ la * W / D := by
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  rw [div_le_div_iff₀ (by linarith) hD]
  have hla : 0 ≤ la := (norm_nonneg _).trans hz
  exact mul_le_mul (mul_le_mul hz hw (abs_nonneg _) hla) hd hD.le (by positivity)

lemma lagrange (c : Fin 3 → ℂ) {t1 t2 t3 g la : ℝ} (hg : 0 < g) (h1 : 1 ≤ t1) (h3 : t3 ≤ 2)
    (h12 : g ≤ t2 - t1) (h23 : g ≤ t3 - t2)
    (p1 : ‖qv c t1‖ ≤ la) (p2 : ‖qv c t2‖ ≤ la) (p3 : ‖qv c t3‖ ≤ la) :
    ‖c‖ ≤ 12 * la / g ^ 2 := by
  have hla : 0 ≤ la := (norm_nonneg _).trans p1
  have d1 : g ^ 2 ≤ |(t1 - t2) * (t1 - t3)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have d2 : g ^ 2 ≤ |(t2 - t1) * (t2 - t3)| := by
    rw [abs_of_nonpos (by nlinarith)]; nlinarith
  have d3 : g ^ 2 ≤ |(t3 - t1) * (t3 - t2)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hg2 : 0 < g ^ 2 := by positivity
  have n1 : ((t1 - t2) * (t1 - t3) : ℂ) ≠ 0 := by
    have : (t1 - t2) * (t1 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d1; linarith
    exact_mod_cast this
  have n2 : ((t2 - t1) * (t2 - t3) : ℂ) ≠ 0 := by
    have : (t2 - t1) * (t2 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d2; linarith
    exact_mod_cast this
  have n3 : ((t3 - t1) * (t3 - t2) : ℂ) ≠ 0 := by
    have : (t3 - t1) * (t3 - t2) ≠ 0 := by intro h; rw [h, abs_zero] at d3; linarith
    exact_mod_cast this
  have a12 : (t1 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a13 : (t1 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a23 : (t2 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a21 : (t2 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a31 : (t3 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a32 : (t3 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have key : ∀ (w1 w2 w3 : ℝ), |w1| ≤ 4 → |w2| ≤ 4 → |w3| ≤ 4 →
      ‖qv c t1 * (w1 : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ) + qv c t2 * (w2 : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * (w3 : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ)‖ ≤ 12 * la / g ^ 2 := by
    intro w1 w2 w3 hw1 hw2 hw3
    refine (norm_add₃_le).trans ?_
    have := term_bd p1 hw1 hg2 d1
    have := term_bd p2 hw2 hg2 d2
    have := term_bd p3 hw3 hg2 d3
    have e : 12 * la / g ^ 2 = la * 4 / g ^ 2 + la * 4 / g ^ 2 + la * 4 / g ^ 2 := by ring
    linarith
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · have := key (t2 * t3) (t1 * t3) (t1 * t2) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
      (by rw [abs_of_nonneg (by nlinarith)]; nlinarith) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
    have e : c 0 = qv c t1 * ((t2 * t3 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((t1 * t3 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((t1 * t2 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 0‖ ≤ _
    rw [e]; exact this
  · have := key (-(t2 + t3)) (-(t1 + t3)) (-(t1 + t2)) (by rw [abs_le]; constructor <;> nlinarith)
      (by rw [abs_le]; constructor <;> nlinarith) (by rw [abs_le]; constructor <;> nlinarith)
    have e : c 1 = qv c t1 * ((-(t2 + t3) : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((-(t1 + t3) : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((-(t1 + t2) : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 1‖ ≤ _
    rw [e]; exact this
  · have := key 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    have e : c 2 = qv c t1 * ((1 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((1 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((1 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 2‖ ≤ _
    rw [e]; exact this

lemma E_closed (c : Fin 3 → ℂ) (la : ℝ) : IsClosed {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} :=
  isClosed_Icc.inter (isClosed_le (continuous_norm.comp (qv_cont c)) continuous_const)

lemma sublevel (c : Fin 3 → ℂ) {la g : ℝ} (hg : 0 < g)
    (hno : ∀ t1 t2 t3 : ℝ, 1 ≤ t1 → t3 ≤ 2 → g ≤ t2 - t1 → g ≤ t3 - t2 → ‖qv c t1‖ ≤ la →
      ‖qv c t2‖ ≤ la → ‖qv c t3‖ ≤ la → False) :
    volume {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} ≤ ENNReal.ofReal (2 * g) := by
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} with hE
  have hcl : IsClosed E := E_closed c la
  have hbdd : BddBelow E := ⟨1, fun t ht => ht.1.1⟩
  rcases E.eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty]; exact bot_le
  set t1 := sInf E with ht1d
  have ht1 : t1 ∈ E := hcl.csInf_mem hne hbdd
  have hge1 : ∀ t ∈ E, t1 ≤ t := fun t ht => csInf_le hbdd ht
  set E2 := E ∩ Ici (t1 + g) with hE2
  rcases E2.eq_empty_or_nonempty with h2 | hne2
  · have hsub : E ⊆ Icc t1 (t1 + g) := by
      intro t ht
      refine ⟨hge1 t ht, ?_⟩
      by_contra hc
      have : t ∈ E2 := ⟨ht, le_of_lt (not_le.mp hc)⟩
      rw [h2] at this; exact this
    calc volume E ≤ volume (Icc t1 (t1 + g)) := measure_mono hsub
      _ = ENNReal.ofReal g := by rw [Real.volume_Icc]; ring_nf
      _ ≤ ENNReal.ofReal (2 * g) := ENNReal.ofReal_le_ofReal (by linarith)
  have hcl2 : IsClosed E2 := hcl.inter isClosed_Ici
  have hbdd2 : BddBelow E2 := ⟨1, fun t ht => ht.1.1.1⟩
  set t2 := sInf E2 with ht2d
  have ht2 : t2 ∈ E2 := hcl2.csInf_mem hne2 hbdd2
  have hge2 : ∀ t ∈ E2, t2 ≤ t := fun t ht => csInf_le hbdd2 ht
  have h12 : t1 + g ≤ t2 := Set.mem_Ici.mp ht2.2
  have hsub : E ⊆ Icc t1 (t1 + g) ∪ Icc t2 (t2 + g) := by
    intro t ht
    by_cases h : t < t1 + g
    · exact Or.inl ⟨hge1 t ht, h.le⟩
    · have htE2 : t ∈ E2 := ⟨ht, not_lt.mp h⟩
      refine Or.inr ⟨hge2 t htE2, ?_⟩
      by_contra hc
      exact hno t1 t2 t ht1.1.1 ht.1.2 (by linarith) (by linarith [not_le.mp hc]) ht1.2 ht2.1.2 ht.2
  calc volume E ≤ volume (Icc t1 (t1 + g) ∪ Icc t2 (t2 + g)) := measure_mono hsub
    _ ≤ volume (Icc t1 (t1 + g)) + volume (Icc t2 (t2 + g)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * g) := by
        rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf

end subgroupData

open subgroupData in
theorem quadraticSublevelDecay' : SUB := by
  intro δ hδ0 hδ1
  refine ⟨22, ?_⟩
  intro c
  set M := ‖c‖ with hMd
  have hM0 : 0 ≤ M := norm_nonneg _
  have hint : ∀ t : ℝ, (1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ) ≤ 1 := fun t =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (c 0 + c 1 * t + c 2 * t ^ 2)])
      (by linarith)
  by_cases hM : M ≤ 1
  · calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
        ≤ ∫⁻ t in Icc (1:ℝ) 2, 1 :=
          setLIntegral_mono' measurableSet_Icc (fun t _ => ENNReal.ofReal_le_one.mpr (hint t))
      _ = 1 := by rw [setLIntegral_const, Real.volume_Icc]; norm_num
      _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := by
          rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
          have : (2:ℝ) ^ (-1:ℝ) ≤ (1 + M) ^ (-δ / 2) := by
            calc (2:ℝ) ^ (-1:ℝ) ≤ 2 ^ (-δ / 2) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
          have h2 : (2:ℝ) ^ (-1:ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
          linarith
  push Not at hM
  set s := M ^ ((1:ℝ) / 4) with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s ^ 4 = M := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hs1 : 1 < s := by
    by_contra h; push Not at h
    have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le h
    linarith
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ s ^ 2} with hE
  have hvol : volume E ≤ ENNReal.ofReal (2 * (5 / s)) := by
    apply sublevel c (by positivity)
    intro t1 t2 t3 h1 h3 h12 h23 p1 p2 p3
    have hl := lagrange c (by positivity) h1 h3 h12 h23 p1 p2 p3
    have e : 12 * s ^ 2 / (5 / s) ^ 2 = 12 * s ^ 4 / 25 := by field_simp; ring
    rw [e, hs4] at hl
    linarith
  have hEm : MeasurableSet E := (E_closed c _).measurableSet
  set K := (1 + s ^ 2) ^ (-δ) with hK
  have pw : ∀ t ∈ Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) ≤
      E.indicator 1 t + ENNReal.ofReal K := by
    intro t ht
    by_cases hp : ‖qv c t‖ ≤ s ^ 2
    · have htE : t ∈ E := ⟨ht, hp⟩
      rw [indicator_of_mem htE]
      exact le_trans (ENNReal.ofReal_le_one.mpr (hint t)) le_self_add
    · refine le_trans ?_ le_add_self
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by
        have : s ^ 2 < ‖qv c t‖ := not_le.mp hp
        simp only [qv] at this; linarith) (by linarith)
  have hfin : 2 * (5 / s) + K ≤ 22 * (1 + M) ^ (-δ / 2) := by
    have hA : K ≤ (1 + M) ^ (-δ / 2) := by
      have e : K = ((1 + s ^ 2) ^ 2) ^ (-δ / 2) := by
        rw [hK, ← Real.rpow_natCast (1 + s ^ 2) 2, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by rw [← hs4]; nlinarith) (by linarith)
    have hB : 1 / (2 * s) ≤ (1 + M) ^ (-δ / 2) := by
      calc 1 / (2 * s) ≤ (1 + s)⁻¹ := by
            rw [one_div]; exact inv_anti₀ (by positivity) (by linarith)
        _ = ((1 + s) ^ 4) ^ (-(1:ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one]; norm_num
        _ ≤ (1 + M) ^ (-(1:ℝ) / 4) := by
            apply Real.rpow_le_rpow_of_nonpos (by linarith) _ (by norm_num)
            rw [← hs4]; nlinarith [pow_pos hs0 3]
        _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e2 : 2 * (5 / s) = 20 * (1 / (2 * s)) := by field_simp; ring
    have hX : 0 ≤ (1 + M) ^ (-δ / 2) := by positivity
    rw [e2]; linarith
  calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
      ≤ ∫⁻ t in Icc (1:ℝ) 2, (E.indicator 1 t + ENNReal.ofReal K) := setLIntegral_mono' measurableSet_Icc pw
    _ = (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) + ∫⁻ _ in Icc (1:ℝ) 2, ENNReal.ofReal K :=
        lintegral_add_right _ measurable_const
    _ ≤ volume E + ENNReal.ofReal K := by
        gcongr
        · calc (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) ≤ ∫⁻ t, E.indicator 1 t := setLIntegral_le_lintegral _ _
            _ = volume E := lintegral_indicator_one hEm
        · rw [setLIntegral_const, Real.volume_Icc]; norm_num
    _ ≤ ENNReal.ofReal (2 * (5 / s)) + ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (2 * (5 / s) + K) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := ENNReal.ofReal_le_ofReal hfin
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.SlowWeightBound
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace PolynomialGrowthIntegrals

lemma int_pos_rpow {R κ : ℝ} (hR : 0 < R) (hκ : κ < 1) :
    ∫⁻ β in Ioc 0 R, ENNReal.ofReal (β ^ (-κ)) = ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
  have hr : (-1 : ℝ) < -κ := by linarith
  have hint : IntegrableOn (fun β : ℝ => β ^ (-κ)) (Ioc 0 R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1 (intervalIntegral.intervalIntegrable_rpow' hr)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] fun β : ℝ => β ^ (-κ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg hx.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl hr)]
  have h1 : -κ + 1 = 1 - κ := by ring
  rw [h1, Real.zero_rpow (by linarith), sub_zero]

lemma int_abs_rpow {R κ : ℝ} (hR : 0 < R) (hκ0 : 0 < κ) (hκ : κ < 1) :
    ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) ≤ 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
  have hpos : ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) =
      ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, ← int_pos_rpow hR hκ]
    exact setLIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [abs_of_pos hx.1]
  have hneg : ∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ)) =
      ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (measurableSet_Icc (a := (0 : ℝ)) (b := R))
      (f := fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ))) (by fun_prop)
    have hs : Neg.neg ⁻¹' Icc (0 : ℝ) R = Icc (-R) 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
    simp only [abs_neg] at h
    rw [hs] at h
    exact h
  calc ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ))
      ≤ (∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
        rw [← Icc_union_Icc_eq_Icc (by linarith : -R ≤ 0) hR.le]
        exact lintegral_union_le _ _ _
    _ = 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by rw [hneg, hpos, two_mul]

lemma fac_le {A b t β β' R : ℝ} (hR : 0 < R) (hA : R ≤ A) (ht : 0 ≤ t) (hβ : |β| ≤ R)
    (hβ' : |β'| ≤ R) :
    (A ^ 2 + (β - b) ^ 2) ^ (-t / 2) ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) := by
  have hA0 : 0 < A := lt_of_lt_of_le hR hA
  have hx : 0 < A ^ 2 + (β - b) ^ 2 := by positivity
  have hy : 0 < A ^ 2 + (β' - b) ^ 2 := by positivity
  have h1 := abs_le.1 hβ
  have h2 := abs_le.1 hβ'
  have hd : (β' - β) ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have h9 : A ^ 2 + (β' - b) ^ 2 ≤ 9 * (A ^ 2 + (β - b) ^ 2) := by
    nlinarith [sq_nonneg ((β' - β) - (β - b))]
  calc (A ^ 2 + (β - b) ^ 2) ^ (-t / 2)
      = 3 ^ t * (9 * (A ^ 2 + (β - b) ^ 2)) ^ (-t / 2) := by
        rw [Real.mul_rpow (by norm_num) hx.le, show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        have h0 : t + 2 * (-t / 2) = 0 := by ring
        rw [h0, Real.rpow_zero, one_mul]
    _ ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy h9 (by linarith)) (by positivity)

lemma slowWeight_le {n : ℕ} {t A b : Fin n → ℝ} {R β β' : ℝ} (hR : 0 < R) (ht : ∀ i, 0 ≤ t i)
    (hA : ∀ i, R ≤ A i) (hβ : |β| ≤ R) (hβ' : |β'| ≤ R) :
    slowly t A b β ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * slowly t A b β' := by
  unfold slowly
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun i _ => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (fac_le hR (hA i) (ht i) hβ hβ')

lemma measurable_slowWeight {n : ℕ} (t A b : Fin n → ℝ) : Measurable (slowly t A b) := by
  unfold slowly
  fun_prop

end PolynomialGrowthIntegrals

open PolynomialGrowthIntegrals in
theorem slowWeightBound' : SLOW := by
  intro n T κ hκ0 hκ1
  refine ⟨3 ^ T / (1 - κ) + 1, fun t A b R hR ht hT hA => ?_⟩
  set f := slowly t A b with hf_def
  set I := ∫⁻ β, f β with hI
  have hfm : Measurable f := measurable_slowWeight t A b
  have hw : Measurable fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ)) := by fun_prop
  set c : ℝ := 3 ^ (∑ i, t i) / (2 * R) with hc
  set q : ℝ := R ^ (1 - κ) / (1 - κ) with hq

  have hcen : ∀ β ∈ Icc (-R) R, f β ≤ ENNReal.ofReal c * I := by
    intro β hβ
    have hb : |β| ≤ R := abs_le.2 ⟨hβ.1, hβ.2⟩
    have key : f β * ENNReal.ofReal (2 * R) ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by
      calc f β * ENNReal.ofReal (2 * R) = ∫⁻ _ in Icc (-R) R, f β := by
            rw [setLIntegral_const, Real.volume_Icc]; congr 2; ring
        _ ≤ ∫⁻ β' in Icc (-R) R, ENNReal.ofReal (3 ^ ∑ i, t i) * f β' :=
            setLIntegral_mono (measurable_const.mul hfm) fun β' hβ' =>
              slowWeight_le hR ht hA hb (abs_le.2 ⟨hβ'.1, hβ'.2⟩)
        _ = ENNReal.ofReal (3 ^ ∑ i, t i) * ∫⁻ β' in Icc (-R) R, f β' := lintegral_const_mul _ hfm
        _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by gcongr; exact setLIntegral_le_lintegral _ _
    have hinv : ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (by positivity), ENNReal.ofReal_one]
    calc f β = f β * ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) := by
          rw [mul_assoc, hinv, mul_one]
      _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I * ENNReal.ofReal (1 / (2 * R)) := by gcongr
      _ = ENNReal.ofReal c * I := by
          rw [hc, div_eq_mul_one_div (3 ^ ∑ i, t i), ENNReal.ofReal_mul (by positivity)]; ring

  have hA1 : ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤
      ENNReal.ofReal (c * (2 * q)) * I := by
    calc ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in Icc (-R) R, ENNReal.ofReal c * I * ENNReal.ofReal (|β| ^ (-κ)) :=
          setLIntegral_mono (measurable_const.mul hw) fun β hβ => by gcongr; exact hcen β hβ
      _ = ENNReal.ofReal c * I * ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) :=
          lintegral_const_mul _ hw
      _ ≤ ENNReal.ofReal c * I * (2 * ENNReal.ofReal q) :=
          by gcongr; exact int_abs_rpow hR hκ0 hκ1
      _ = ENNReal.ofReal (c * (2 * q)) * I := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          try ring

  have hA2 : ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤ ENNReal.ofReal (R ^ (-κ)) * I := by
    calc ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (R ^ (-κ)) := by
          refine setLIntegral_mono (hfm.mul measurable_const) fun β hβ => ?_
          have hb : R < |β| := by
            by_contra h
            exact hβ (abs_le.1 (not_lt.1 h))
          gcongr f β * ?_
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hR hb.le (by linarith))
      _ = (∫⁻ β in (Icc (-R) R)ᶜ, f β) * ENNReal.ofReal (R ^ (-κ)) := lintegral_mul_const _ hfm
      _ ≤ I * ENNReal.ofReal (R ^ (-κ)) := by gcongr; exact setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (R ^ (-κ)) * I := mul_comm _ _

  have hRk : R ^ (1 - κ) = R * R ^ (-κ) := by
    rw [show 1 - κ = 1 + -κ by ring, Real.rpow_add hR, Real.rpow_one]
  have hcq : c * (2 * q) = 3 ^ (∑ i, t i) * R ^ (-κ) / (1 - κ) := by
    rw [hc, hq, hRk]
    have : (1 - κ) ≠ 0 := by linarith
    field_simp
    try ring
  have hsT : (3 : ℝ) ^ (∑ i, t i) ≤ 3 ^ T := Real.rpow_le_rpow_of_exponent_le (by norm_num) hT
  have hRp : 0 < R ^ (-κ) := Real.rpow_pos_of_pos hR _
  have hreal : c * (2 * q) + R ^ (-κ) ≤ (3 ^ T / (1 - κ) + 1) * R ^ (-κ) := by
    rw [hcq, add_mul, one_mul, div_mul_eq_mul_div]
    gcongr
    try linarith
  calc ∫⁻ β, slowly t A b β * ENNReal.ofReal (|β| ^ (-κ))
      = (∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) :=
        (lintegral_add_compl (fun β => f β * ENNReal.ofReal (|β| ^ (-κ))) measurableSet_Icc).symm
    _ ≤ ENNReal.ofReal (c * (2 * q)) * I + ENNReal.ofReal (R ^ (-κ)) * I := add_le_add hA1 hA2
    _ = ENNReal.ofReal (c * (2 * q) + R ^ (-κ)) * I := by
        rw [ENNReal.ofReal_add (by positivity) hRp.le, add_mul]
    _ ≤ ENNReal.ofReal ((3 ^ T / (1 - κ) + 1) * R ^ (-κ)) * I :=
        by gcongr
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

