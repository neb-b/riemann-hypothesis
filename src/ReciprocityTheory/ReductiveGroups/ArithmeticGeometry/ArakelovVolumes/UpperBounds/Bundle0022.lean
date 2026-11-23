module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfB

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem measInv_holds : MeasInvStatement (E := E) := by
  intro r X x0 x0' h0 h0' φ hφm hφ
  exact MI.lintegral_cpt_muX_indep_of_isOrtho X h0 h0' hφm hφ

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem norm_chi {la : Wt X.Ψ r} {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp this

theorem conj_chi {la : Wt X.Ψ r} {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (starRingEnd ℂ) (X.χ la γ) = (X.χ la γ)⁻¹ := by
  have h := norm_chi X (la := la) hγ
  have hn : Complex.normSq (X.χ la γ) = 1 := by rw [Complex.normSq_eq_norm_sq, h, one_pow]
  rw [Complex.inv_def, hn, inv_one, Complex.ofReal_one, mul_one]

theorem meas_indC {f : Frame X.Ψ r → ℂ} (hf : ContinuousOn f X.dom) : Measurable (X.dom.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hf.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

def Gu (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) (x : Frame X.Ψ r) : ℂ :=
  X.dom.indicator P x * (starRingEnd ℂ) (X.dom.indicator f0 x) * ((W x).toReal : ℂ)

def phi0 (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (‖X.dom.indicator f0 x‖ ^ 2) * W x

theorem Gu_dom {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Gu X P f0 W x = P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ) := by
  simp [Gu, Set.indicator_of_mem hx]

theorem unfoldedDensity_on_dom {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi0 X f0 W x = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by
  simp [phi0, Set.indicator_of_mem hx]

theorem Gu_meas {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hP : ContinuousOn P X.dom)
    (hf : ContinuousOn f0 X.dom) (hW : Measurable W) : Measurable (Gu X P f0 W) :=
  ((meas_indC X hP).mul (Complex.continuous_conj.measurable.comp (meas_indC X hf))).mul
    (Complex.measurable_ofReal.comp hW.ennreal_toReal)

theorem measurable_unfoldedDensity {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hf : ContinuousOn f0 X.dom)
    (hW : Measurable W) : Measurable (phi0 X f0 W) :=
  (ENNReal.measurable_ofReal.comp ((meas_indC X hf).norm.pow_const 2)).mul hW

theorem Gu_rmul {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2))
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    Gu X P f0 W (rmul x b) = Gu X P f0 W x := by
  rw [Gu_dom X (OrthogonalFrameDomain.rmul_mem_dom X hx hb), Gu_dom X hx, hP x hx b hb, hf x hx b hb, hW x hx b hb]
  have hc : bchar la b ≠ 0 := bchar_ne X hb la
  have hn : (‖bchar la b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
  have hcc : bchar la b * (starRingEnd ℂ) (bchar la b) = (‖bchar la b‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), map_mul]
  push_cast
  rw [show bchar la b * P x * ((starRingEnd ℂ) (bchar la b) * (starRingEnd ℂ) (f0 x)) *
      (((W x).toReal : ℂ) / (‖bchar la b‖ : ℂ) ^ 2) = (bchar la b * (starRingEnd ℂ) (bchar la b)) *
      (P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ)) / (‖bchar la b‖ : ℂ) ^ 2 by ring, hcc]
  field_simp

theorem unfoldedDensity_borel_invariant {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2))
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phi0 X f0 W (rmul x b) = phi0 X f0 W x := by
  rw [unfoldedDensity_on_dom X (OrthogonalFrameDomain.rmul_mem_dom X hx hb), unfoldedDensity_on_dom X hx, hf x hx b hb, hW x hx b hb]
  have hc : bchar la b ≠ 0 := bchar_ne X hb la
  have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (norm_pos_iff.mpr hc) 2
  rw [norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity)]
  rw [show ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖f0 x‖ ^ 2) *
      (W x / ENNReal.ofReal (‖bchar la b‖ ^ 2)) = ENNReal.ofReal (‖f0 x‖ ^ 2) *
      (W x / ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖bchar la b‖ ^ 2)) by ring,
    ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top]

theorem unfoldedDensity_gamma_invariant {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, W (lact γ x) = W x)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi0 X f0 W (lact γ x) = phi0 X f0 W x := by
  rw [unfoldedDensity_on_dom X ((lact_mem_dom_iff X hγ x).mpr hx), unfoldedDensity_on_dom X hx, hf γ hγ x hx, hW γ hγ x hx,
    norm_mul, norm_chi X hγ, one_mul]

theorem ineq_pt (a b : ℂ) (w : ℝ≥0∞) {k : ℝ} (hk : 0 < k) :
    ‖a * (starRingEnd ℂ) b * ((w.toReal : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal (‖a‖ ^ 2 / k) * w + ENNReal.ofReal k * (ENNReal.ofReal (‖b‖ ^ 2) * w) := by
  rcases eq_or_ne w ⊤ with rfl | hw
  · simp
  · have hw' : w = ENNReal.ofReal w.toReal := (ENNReal.ofReal_toReal hw).symm
    have ht : 0 ≤ w.toReal := ENNReal.toReal_nonneg
    rw [← ofReal_norm]
    conv_rhs => rw [hw']
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hk.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg ht]
    have hA := norm_nonneg a
    have hB := norm_nonneg b
    have h1 : ‖a‖ ^ 2 / k + k * ‖b‖ ^ 2 - 2 * (‖a‖ * ‖b‖) = (‖a‖ - k * ‖b‖) ^ 2 / k := by
      field_simp; ring
    have h2 : 0 ≤ (‖a‖ - k * ‖b‖) ^ 2 / k := div_nonneg (sq_nonneg _) hk.le
    have h3 : 0 ≤ ‖a‖ ^ 2 / k + k * ‖b‖ ^ 2 - ‖a‖ * ‖b‖ := by nlinarith [mul_nonneg hA hB]
    nlinarith [mul_nonneg ht h3]

theorem enorm_ind_mul {M : Set (Frame X.Ψ r)} (y : Frame X.Ψ r) (c : ℂ) :
    ‖M.indicator (1 : Frame X.Ψ r → ℂ) y * c‖ₑ = M.indicator (1 : Frame X.Ψ r → ℝ≥0∞) y * ‖c‖ₑ := by
  by_cases h : y ∈ M
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

theorem ka_meas (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaF X x0 bb) := by
  have hd : ∀ τ : X.Ψ, Measurable fun z => dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ :=
    fun τ => ((ExtFPf.cont_dmin X τ _).comp (cpt_cont X x0)).measurable
  unfold kaF rhF
  exact Real.measurable_exp.comp (measurable_const.mul
    (Finset.measurable_sum _ fun τ _ => Real.measurable_log.comp (hd τ).norm).neg)

theorem pairUnfold_of (hM : MeasInvStatement (E := E)) (hK : KaUnfoldStatement (E := E))
    (hLU : LUStatement (E := E)) : PairUnfoldStatement (E := E) := by
  intro r X x0 hx0 hPD la W bb hW hWl hbb F P hF hInAt hP hPF FF hFF f0 hf0 hf0FF
  obtain ⟨D⟩ := ExtFPf.luData_of hLU X x0 hx0
  have hf0S : X.IsSec la f0 := hf0.1.1
  have hGm : Measurable (Gu X P f0 W) := Gu_meas X hP.1.continuousOn hf0S.1.continuousOn hW.1
  have hGB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Gu X P f0 W (rmul x b) = Gu X P f0 W x :=
    fun x hx b hb => Gu_rmul X hP.2 hf0S.2.1 hW.2.1 hx hb
  have hnB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ‖Gu X P f0 W (rmul x b)‖ₑ = ‖Gu X P f0 W x‖ₑ :=
    fun x hx b hb => by rw [hGB x hx b hb]
  have hG_lact : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Gu X P f0 W (lact γ x) =
      (X.χ la γ)⁻¹ * P (lact γ x) * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ) := by
    intro γ hγ x hx
    rw [Gu_dom X ((lact_mem_dom_iff X hγ x).mpr hx), hf0S.2.2 γ hγ x hx, hW.2.2 γ hγ x hx, map_mul,
      conj_chi X hγ]
    ring

  have hfin : ∫⁻ z, ‖Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0 < ⊤ := by
    obtain ⟨C, hC, hCle⟩ := hK r X x0 hx0 hPD FF hFF bb hbb
    have hI2 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * phi0 X f0 W (cpt X x0 z) ∂muF X x0 < ⊤ := by
      refine lt_of_le_of_lt (hCle _ (measurable_unfoldedDensity X hf0S.1.continuousOn hW.1)
        (fun x hx b hb => unfoldedDensity_borel_invariant X hf0S.2.1 hW.2.1 hx hb)
        (fun γ hγ x hx => unfoldedDensity_gamma_invariant X hf0S.2.2 hW.2.2 hγ hx)) (ENNReal.mul_lt_top hC ?_)
      have : ∫⁻ z in FF, phi0 X f0 W (cpt X x0 z) ∂muF X x0 =
          ∫⁻ z in FF, ENNReal.ofReal (‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 :=
        setLIntegral_congr_fun hFF.1 fun z hz => unfoldedDensity_on_dom X (hFF.2.1 hz)
      rw [this]; exact hf0FF
    calc ∫⁻ z, ‖Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0
        ≤ ∫⁻ z, (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) +
            ENNReal.ofReal (kaF X x0 bb z) * phi0 X f0 W (cpt X x0 z)) ∂muF X x0 := by
          refine lintegral_mono_ae ?_
          filter_upwards [ExtFPf.ae_OmF] with z hz
          rw [Gu_dom X hz, unfoldedDensity_on_dom X hz, hPF z hz]
          exact ineq_pt _ _ _ (Real.exp_pos _)
      _ = ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 +
            ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * phi0 X f0 W (cpt X x0 z) ∂muF X x0 :=
          lintegral_add_right _ ((ENNReal.measurable_ofReal.comp (ka_meas X x0 bb)).mul
            ((measurable_unfoldedDensity X hf0S.1.continuousOn hW.1).comp (cpt_cont X x0).measurable))
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hInAt, hI2⟩
  have hsum1 : ∑' γ : X.Γ, ∫⁻ z in FF, ‖Gu X P f0 W (lact γ.1 (cpt X x0 z))‖ₑ ∂muF X x0 < ⊤ := by
    rw [lunfold D FF hM hx0 hFF (fun x => ‖Gu X P f0 W x‖ₑ) hGm.enorm hnB]; exact hfin

  have hL : Set.EqOn (fun z => poin X la P (cpt X x0 z) * (starRingEnd ℂ) (f0 (cpt X x0 z)) *
      ((W (cpt X x0 z)).toReal : ℂ)) (fun z => ∑' γ : X.Γ, Gu X P f0 W (lact γ.1 (cpt X x0 z))) FF := by
    intro z hz
    have hzd : cpt X x0 z ∈ X.dom := hFF.2.1 hz
    simp only [poin]
    rw [← tsum_mul_right, ← tsum_mul_right]
    exact tsum_congr fun γ => (hG_lact γ.1 γ.2 _ hzd).symm
  rw [setIntegral_congr_fun hFF.1 hL]
  have hmeas1 : ∀ γ : X.Γ, AEStronglyMeasurable (fun z => Gu X P f0 W (lact γ.1 (cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hGm.comp ((lact_cont X γ.1).comp (cpt_cont X x0)).measurable).aestronglyMeasurable
  rw [integral_tsum hmeas1 hsum1.ne]
  have hcu : ∀ γ : X.Γ, ∫ z in FF, Gu X P f0 W (lact γ.1 (cpt X x0 z)) ∂muF X x0 =
      ∫ z, (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ.1⁻¹ (cpt X x0 z)) * Gu X P f0 W (cpt X x0 z)
        ∂muF X x0 := fun γ => cunfold_one D FF hM hx0 hFF _ hGm hGB γ.2
  rw [tsum_congr hcu]
  have hmeas2 : ∀ γ : X.Γ, AEStronglyMeasurable (fun z => (T D FF).indicator (1 : Frame X.Ψ r → ℂ)
      (lact γ.1⁻¹ (cpt X x0 z)) * Gu X P f0 W (cpt X x0 z)) (muF X x0) := by
    intro γ
    have h1 : Measurable ((T D FF).indicator (1 : Frame X.Ψ r → ℂ)) :=
      measurable_one.indicator (T_meas D FF hFF.1)
    have h2 : Measurable fun z => lact γ.1⁻¹ (cpt X x0 z) :=
      ((lact_cont X γ.1⁻¹).comp (cpt_cont X x0)).measurable
    exact ((h1.comp h2).mul (hGm.comp (cpt_cont X x0).measurable)).aestronglyMeasurable
  have hsum2 : ∑' γ : X.Γ, ∫⁻ z, ‖(T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ.1⁻¹ (cpt X x0 z)) *
      Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0 ≠ ⊤ := by
    have : ∀ γ : X.Γ, ∫⁻ z, ‖(T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ.1⁻¹ (cpt X x0 z)) *
        Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0 =
        ∫⁻ z in FF, ‖Gu X P f0 W (lact γ.1 (cpt X x0 z))‖ₑ ∂muF X x0 := fun γ => by
      rw [lunfold_one D FF hM hx0 hFF (fun x => ‖Gu X P f0 W x‖ₑ) hGm.enorm hnB γ.2]
      simp only [enorm_ind_mul]
    rw [tsum_congr this]; exact hsum1.ne
  rw [← integral_tsum hmeas2 hsum2]
  refine integral_congr_ae ?_
  filter_upwards [ae_unique D FF hFF] with z ⟨hzO, γ0, hγ0, hu⟩
  rw [tsum_eq_single ⟨γ0, hγ0⟩]
  · rw [Set.indicator_of_mem ((hu γ0 hγ0).mpr rfl), Pi.one_apply, one_mul, Gu_dom X hzO, hPF z hzO]
  · intro γ hne
    rw [Set.indicator_of_notMem, zero_mul]
    intro h
    exact hne (Subtype.ext ((hu γ.1 γ.2).mp h))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Hyp (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  IsOrth X x0 ∧ PropDisc X ∧ IsMetricW X la W ∧ WLower X la W ∧
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
    IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def supR (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (ρ : ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)

def LocStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ x ∈ X.dom, ∃ ε > 0, ∃ u : X.Γ → ℝ, Summable u ∧
      ∀ γ : X.Γ, ∀ y ∈ Metric.ball x ε, ‖P (lact γ.1 y)‖ ≤ u γ

def BallStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ ≤ ENNReal.ofReal C * supR X la W ρ x

def FFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)

theorem differentiable_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Differentiable ℂ (lact (Ψ := Ψ) γ) := by
  unfold lact mat
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem enorm_poin_le (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    ENNReal.ofReal ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
  unfold poin
  have hχ : ∀ γ : X.Γ, ‖X.χ la γ.1‖ = 1 := fun γ => by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1
      (by rw [← norm_pow, h γ.1 γ.2, norm_one])
  have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := fun γ => by
    rw [norm_mul, norm_inv, hχ γ, inv_one, one_mul]
  by_cases hs : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖
  · calc ENNReal.ofReal ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖
        ≤ ENNReal.ofReal (∑' γ : X.Γ, ‖P (lact γ.1 x)‖) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hn))
          exact hs.congr fun γ => (hn γ).symm
      _ = ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
          simp only [ofReal_norm_eq_enorm]
  · have htop : ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ = ⊤ := by
      by_contra h
      apply hs
      have h2 : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖₊ := by
        rw [← ENNReal.tsum_coe_ne_top_iff_summable]
        simpa only [enorm_eq_nnnorm] using h
      exact NNReal.summable_coe.2 h2
    rw [htop]
    exact le_top

theorem supR_le (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    (hW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) (ρ : ℝ) (x : Frame X.Ψ r) :
    supR X la W ρ x ≤ ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) := by
  unfold supR
  refine iSup₂_le fun z _ => iSup_le fun hz => ENNReal.rpow_le_rpow ?_ (by norm_num)
  have he : 0 < Real.exp (-phla X la (cpt X x z)) := Real.exp_pos _
  calc ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)
      ≤ ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) /
          ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x z))) := ENNReal.div_le_div_left (hW _ hz) _
    _ = ENNReal.ofReal (1 / c) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_sgn' (p0 a : ℕ) : ‖((sgn p0 a : ℝ) : ℂ)‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem norm_dmin_orth' (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold IsOrth at hx
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  exact Finset.prod_eq_one fun a _ => norm_sgn' _ _

theorem pnorm_orth' (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  simp [norm_div, norm_dmin_orth' X hx]

theorem poin_of (hL : LocStatement (E := E)) (hB : BallStatement (E := E)) (hF : FFStatement (E := E)) :
    PoinStatement (E := E) := by
  intro r X x0 hx0 hPD la W bb hW hWl hbb F P hFd hA hP hPF
  have H : Hyp X x0 la W bb F P := ⟨hx0, hPD, hW, hWl, hbb, hFd, hA, hP, hPF⟩
  obtain ⟨c, hc, hcW⟩ := hWl
  have hterm : ∀ (γ : X.Γ) y, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ := by
    intro γ y; rw [norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
  obtain ⟨C1, hC1⟩ := hB r X x0 la W bb F P H 1 one_pos le_rfl
  have horth : ∀ y ∈ X.dom, IsOrth X y → ‖poin X la P y‖ ≤ max C1 0 * (1 / c) ^ (1 / 2 : ℝ) := by
    intro y hy hyo
    have h1 := (enorm_poin_le X la P y).trans ((hC1 y hy hyo).trans
      (mul_le_mul_of_nonneg_left (supR_le X la W hc hcW 1 y) (zero_le)))
    have h2 : ENNReal.ofReal C1 * ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (max C1 0 * (1 / c) ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_mul (le_max_right _ _)]
      gcongr
      exact le_max_left _ _
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)
  refine ⟨?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hF r X x0 la W bb F P H, ?_, ?_⟩
  · intro x hx
    obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun γ => (hterm γ x).le.trans (hub γ x (Metric.mem_ball_self hε))) hu
  · unfold poin
    refine differentiableOn_tsum_loc (isOpenDom X) _ (fun γ => ?_) (fun x hx => ?_)
    · exact (differentiableOn_const _).mul
        (hP.1.comp (differentiable_lact γ.1).differentiableOn fun y hy => lactDom X γ.2 hy)
    · obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
      exact ⟨ε, hε, u, hu, fun γ y hy => (hterm γ y).le.trans (hub γ y hy)⟩
  · intro x hx b hb
    exact poin_rmul X la P hP.2 hx hb
  · intro γ hγ x _
    exact poin_lact X la P hγ x
  · refine ⟨max C1 0 * (1 / c) ^ (1 / 2 : ℝ), fun x hx => ?_⟩
    have hb := FrameDegreeData.bOf_mem X hx
    have ho : IsOrth X (rmul x (FrameDegreeData.bOf X x)) := FrameDegreeData.ortho_bOf X hx
    have hxb : rmul x (FrameDegreeData.bOf X x) ∈ X.dom := rmulDom X hb hx
    rw [← FrameDegreeData.pnorm_rmul X la _ (fun y hy b hb => poin_rmul X la P hP.2 hy hb) x hx _ hb,
      pnorm_orth' X la _ ho]
    exact horth _ hxb ho
  · intro ρ hρ hρ1
    obtain ⟨C, hC⟩ := hB r X x0 la W bb F P H ρ hρ hρ1
    exact ⟨C, fun x hx hxo => (enorm_poin_le X la P x).trans (hC x hx hxo)⟩
  · intro la' g hg x hx
    exact poin_mul X la la' P g hg x hx

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

