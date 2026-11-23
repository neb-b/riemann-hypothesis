module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up.MI ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable FM.haarF FM.haarIx

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem FrameMeasStatement_holds : FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hC hCd
  have hx0' : X.IsOrtho x0 := hx0
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  obtain ⟨R1, hR1⟩ := β0_bound (X := X) hC hCd
  have hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ max R1 0 :=
    fun x hx τ a b => (hR1 x hx τ a b).trans (le_max_left _ _)
  have hKR : KR X (max R1 0) ≠ ⊤ := (KR_lt_top (X := X) (le_max_right R1 0)).ne
  have hdet : ∀ τ, (mat x0 τ).det ≠ 0 := by
    intro τ h
    have h1 := normSq_det_orthogonalFrame (X := X) hx0' τ
    rw [h, map_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hU0 : ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have hΦ0 : ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have hP : (∏ τ, (mat x0 τ).det ^ r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hdet τ)
  have hA0 : ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Complex.normSq_pos.mpr hP))).ne'
  refine ⟨((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
      (ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹)⁻¹ * KR X (max R1 0) *
      ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹, ?_, ?_⟩
  · exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr hU0) (ENNReal.inv_ne_top.mpr hA0)) hKR)
      (ENNReal.inv_ne_top.mpr hΦ0)).lt_top
  intro G hGm hGinv
  have hFm : Measurable (C.indicator G) := hGm.indicator hCm
  have hφm : Measurable ({p | Jp X C p ≠ 0}.indicator G) :=
    hGm.indicator ((measurable_Jp (X := X) hCm) (measurableSet_singleton 0).compl)

  have hUf : ∫⁻ v, C.indicator G (ufC X v) =
      ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ x, C.indicator G x := lintegral_ufC (X := X) (C.indicator G)
  have hLA : ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) =
      ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ *
        ∫⁻ v, C.indicator G (ufC X v) :=
    lintegral_comp_LA (fun τ => mat x0 τ) hdet (hFm.comp (ufC X).continuous.measurable)
  have hgm : Measurable (fun v => C.indicator G (ufC X (LA (fun τ => mat x0 τ) v))) :=
    hFm.comp ((ufC X).continuous.measurable.comp
      (LinearMap.continuous_of_finiteDimensional _).measurable)
  have hin : ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) ≤
      KR X (max R1 0) * ∫⁻ x, GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
    refine le_trans (le_of_eq (lintegral_flat hgm)) ?_
    rw [← lintegral_const_mul' _ _ hKR]
    exact lintegral_mono fun x => inner_le (X := X) hx0' hCm hCd hR0 hGinv x
  have hmuX := lintegral_muX (X := X) (x0 := x0) hφm
  have hlast : ∫⁻ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ∂muX X x0 ≤
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    have hpt : ∀ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ≤
        (sat X x0 C).indicator (fun z => G (cpt X x0 z)) z := by
      intro z
      by_cases hJ : Jp X C (cpt X x0 z) = 0
      · have h0 : ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) = 0 :=
          Set.indicator_apply_eq_zero.mpr fun h => (h hJ).elim
        rw [h0]
        exact zero_le
      · have hz : z ∈ sat X x0 C := by
          by_contra hz
          apply hJ
          apply Jp_eq_zero (X := X)
          intro y hy hyC
          exact hz (mem_sat (X := X) hCd hy hyC)
        rw [Set.indicator_of_mem (show cpt X x0 z ∈ {p | Jp X C p ≠ 0} from hJ),
          Set.indicator_of_mem hz]
    exact (lintegral_mono hpt).trans (lintegral_indicator_le _ _)
  have e1 : ∫⁻ x, C.indicator G x =
      ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ∫⁻ v, C.indicator G (ufC X v) := by
    rw [hUf, ← mul_assoc, ENNReal.inv_mul_cancel hU0 ENNReal.coe_ne_top, one_mul]
  have e2 : ∫⁻ v, C.indicator G (ufC X v) =
      (ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹)⁻¹ *
        ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) := by
    rw [hLA, ← mul_assoc, ENNReal.inv_mul_cancel hA0 ENNReal.ofReal_ne_top, one_mul]
  have e4 : ∫⁻ x, GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x =
      ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ∫⁻ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ∂muX X x0 := by
    rw [hmuX, ← mul_assoc, ENNReal.inv_mul_cancel hΦ0 ENNReal.coe_ne_top, one_mul]
  rw [← lintegral_indicator (f := G) hCm, e1, e2, mul_assoc, mul_assoc, mul_assoc]
  gcongr
  refine hin.trans ?_
  rw [e4]
  gcongr
  all_goals exact hlast

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem wdb_contDiffOn (hU : IsOpen U) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g U) (k : Fin n) :
    ContDiffOn ℝ ∞ (wdb n k g) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (bas n k)) U := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (Complex.I • bas n k)) U :=
    hd.clm_apply contDiffOn_const
  show ContDiffOn ℝ ∞
    (fun y => (fderiv ℝ g y (bas n k) + Complex.I * fderiv ℝ g y (Complex.I • bas n k)) / 2) U
  exact (h1.add (contDiffOn_const.mul h2)).div_const 2

theorem wd_continuousOn (hU : IsOpen U) {h : V n → ℂ} (hh : ContDiffOn ℝ ∞ h U) (j : Fin n) :
    ContinuousOn (wd n j h) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hh).2
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y (bas n j)) U := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y (Complex.I • bas n j)) U :=
    hd.clm_apply contDiffOn_const
  show ContinuousOn
    (fun y => (fderiv ℝ h y (bas n j) - Complex.I * fderiv ℝ h y (Complex.I • bas n j)) / 2) U
  exact ((h1.sub (contDiffOn_const.mul h2)).div_const 2).continuousOn

theorem leviV_scale (g : V n → ℂ) (z : V n) (t : ℝ) (ξ : Fin n → ℂ) :
    (leviV n g z (fun j => (t : ℂ) * ξ j)).re = t ^ 2 * (leviV n g z ξ).re := by
  have h : leviV n g z (fun j => (t : ℂ) * ξ j) = ((t ^ 2 : ℝ) : ℂ) * leviV n g z ξ := by
    simp only [leviV, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]

theorem levi_unif (hU : IsOpen U) {g : V n → ℝ} (hg : ContDiffOn ℝ ∞ g U) {K : Set (V n)}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ z ∈ K, ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => (g w : ℂ)) z ξ).re) :
    ∃ c > 0, ∀ z ∈ K, ∀ ξ : Fin n → ℂ,
      c * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (g w : ℂ)) z ξ).re := by
  have hG : ContDiffOn ℝ ∞ (fun w => (g w : ℂ)) U :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hg).congr (fun x _ => by simp)
  have hcont : ContinuousOn
      (fun p : V n × (Fin n → ℂ) => (leviV n (fun w => (g w : ℂ)) p.1 p.2).re)
      (K ×ˢ sphere (0 : Fin n → ℂ) 1) := by
    refine Complex.continuous_re.comp_continuousOn
      (f := fun p : V n × (Fin n → ℂ) => leviV n (fun w => (g w : ℂ)) p.1 p.2) ?_
    show ContinuousOn (fun p : V n × (Fin n → ℂ) => ∑ j, ∑ k,
      wd n j (wdb n k (fun w => (g w : ℂ))) p.1 * p.2 j * (starRingEnd ℂ) (p.2 k)) _
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    have hw : ContinuousOn
        (fun p : V n × (Fin n → ℂ) => wd n j (wdb n k (fun w => (g w : ℂ))) p.1)
        (K ×ˢ sphere (0 : Fin n → ℂ) 1) :=
      (wd_continuousOn hU (wdb_contDiffOn hU hG k) j).comp continuousOn_fst
        (fun p hp => hKU hp.1)
    refine (hw.mul ?_).mul ?_
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
    · exact (Complex.continuous_conj.comp ((continuous_apply k).comp continuous_snd)).continuousOn
  by_cases hne : (K ×ˢ sphere (0 : Fin n → ℂ) 1).Nonempty
  · obtain ⟨p0, hp0, hmin⟩ :=
      (hK.prod (isCompact_sphere (0 : Fin n → ℂ) 1)).exists_isMinOn hne hcont
    have hp0ne : p0.2 ≠ 0 := by
      intro h
      have h1 := hp0.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at h1
      exact zero_ne_one h1
    have hc0 : 0 < (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re := hpos p0.1 hp0.1 p0.2 hp0ne
    refine ⟨(leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1),
      div_pos hc0 (by positivity), ?_⟩
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hη : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
      have hm : (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re
          ≤ (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re :=
        isMinOn_iff.1 hmin (z, ‖ξ‖⁻¹ • ξ) (Set.mk_mem_prod hz hη)
      have hξη : (fun j => ((‖ξ‖ : ℝ) : ℂ) * (‖ξ‖⁻¹ • ξ) j) = ξ := by
        funext j
        rw [Pi.smul_apply, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_mul]
      have key : (leviV n (fun w => (g w : ℂ)) z ξ).re
          = ‖ξ‖ ^ 2 * (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re :=
        (congrArg (fun v => (leviV n (fun w => (g w : ℂ)) z v).re) hξη.symm).trans
          (leviV_scale (fun w => (g w : ℂ)) z ‖ξ‖ (‖ξ‖⁻¹ • ξ))
      have hsum : ∑ j, ‖ξ j‖ ^ 2 ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by
        calc ∑ j, ‖ξ j‖ ^ 2 ≤ ∑ _j : Fin n, ‖ξ‖ ^ 2 :=
              Finset.sum_le_sum fun j _ => by gcongr; exact norm_le_pi_norm ξ j
          _ = (n : ℝ) * ‖ξ‖ ^ 2 := by simp
          _ ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
      rw [key]
      calc (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1) * ∑ j, ‖ξ j‖ ^ 2
          ≤ (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1)
              * (((n : ℝ) + 1) * ‖ξ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum (div_pos hc0 (by positivity)).le
        _ = (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re * ‖ξ‖ ^ 2 := by
            rw [← mul_assoc, div_mul_cancel₀ _ (by positivity : ((n : ℝ) + 1) ≠ 0)]
        _ ≤ ‖ξ‖ ^ 2 * (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re := by
            nlinarith [hm, sq_nonneg ‖ξ‖]
  · refine ⟨1, one_pos, ?_⟩
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · exfalso
      apply hne
      refine ⟨(z, ‖ξ‖⁻¹ • ξ), hz, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_iff.2 hξ).ne']

private theorem eq_zero_on_ball_of_eventuallyEq_zero {F : V n → ℂ} {w : V n} {ρ : ℝ}
    (hF : DifferentiableOn ℂ F (ball w ρ)) (h0 : F =ᶠ[𝓝 w] 0) :
    ∀ y ∈ ball w ρ, F y = 0 := by
  intro y hy
  by_cases hyw : y = w
  · subst hyw
    exact h0.self_of_nhds
  have hρ : 0 < ρ := pos_of_mem_ball hy
  have hd : 0 < ‖y - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hyw)
  have hyd : ‖y - w‖ < ρ := by rw [← dist_eq_norm]; exact hy
  have hmaps : Set.MapsTo (fun t : ℂ => w + t • (y - w)) (ball (0 : ℂ) (ρ / ‖y - w‖)) (ball w ρ) := by
    intro t ht
    rw [mem_ball, dist_zero_right, lt_div_iff₀ hd] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hLd : Differentiable ℂ (fun t : ℂ => w + t • (y - w)) := by fun_prop
  have hg : DifferentiableOn ℂ (fun t : ℂ => F (w + t • (y - w))) (ball (0 : ℂ) (ρ / ‖y - w‖)) :=
    hF.comp hLd.differentiableOn hmaps
  have hT : Filter.Tendsto (fun t : ℂ => w + t • (y - w)) (𝓝 0) (𝓝 w) := by
    have h := hLd.continuous.tendsto 0
    rwa [zero_smul, add_zero] at h
  have hg0 : (fun t : ℂ => F (w + t • (y - w))) =ᶠ[𝓝 0] 0 := h0.comp_tendsto hT
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (ρ / ‖y - w‖) := by
    rw [mem_ball, dist_zero_right, norm_one, lt_div_iff₀ hd, one_mul]
    exact hyd
  have h2 := (hg.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) _).isPreconnected (mem_ball_self (div_pos hρ hd)) hg0 h1
  simpa using h2

theorem ident_preconn (hU : IsOpen U) (hc : IsPreconnected U) {F : V n → ℂ}
    (hF : DifferentiableOn ℂ F U) {a : V n} (ha : a ∈ U) (h0 : F =ᶠ[𝓝 a] 0) : Set.EqOn F 0 U := by
  have hS : IsOpen {z : V n | F =ᶠ[𝓝 z] 0} := isOpen_setOf_eventually_nhds
  have hcl : closure {z : V n | F =ᶠ[𝓝 z] 0} ∩ U ⊆ {z : V n | F =ᶠ[𝓝 z] 0} := by
    rintro z ⟨hzc, hzU⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨w, hwS, hzw⟩ := Metric.mem_closure_iff.1 hzc (r / 2) (half_pos hr)
    have hsub : ball w (r / 2) ⊆ U := by
      intro y hy
      apply hrU
      rw [mem_ball] at hy ⊢
      calc dist y z ≤ dist y w + dist w z := dist_triangle _ _ _
        _ < r / 2 + r / 2 := by rw [dist_comm w z]; exact add_lt_add hy hzw
        _ = r := add_halves r
    have hzb : z ∈ ball w (r / 2) := by rw [mem_ball]; exact hzw
    have hw0 : F =ᶠ[𝓝 w] 0 := hwS
    show F =ᶠ[𝓝 z] 0
    exact Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb)
      (fun y hy => eq_zero_on_ball_of_eventuallyEq_zero (hF.mono hsub) hw0 y hy)
  have hUS := hc.subset_of_closure_inter_subset hS ⟨a, ha, h0⟩ hcl
  intro z hz
  have h' : F =ᶠ[𝓝 z] 0 := hUS hz
  exact h'.self_of_nhds

theorem hgn_of (hU : IsOpen U) (hc : IsPreconnected U) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    {a : V n} (ha : a ∈ U) (hne : ¬ F =ᶠ[𝓝 a] 0) :
    ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, F y ≠ 0 := by
  intro W hW hWU hWne
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hWne
  have hy0 : F =ᶠ[𝓝 y] 0 := Filter.eventually_of_mem (hW.mem_nhds hy) (fun x hx => hcon x hx)
  have hall := ident_preconn hU hc hF (hWU hy) hy0
  exact hne (Filter.eventually_of_mem (hU.mem_nhds ha) (fun x hx => hall hx))

theorem ker_bot_of_det {f' : V n →L[ℂ] V n} (hdet : f'.det ≠ 0) :
    LinearMap.ker (f' : V n →ₗ[ℂ] V n) = ⊥ := by
  exact (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))

theorem iso_zero {f : V n → V n} {f' : V n →L[ℂ] V n} (hf : HasFDerivAt f f' 0) (hdet : f'.det ≠ 0)
    (h0 : f 0 = 0) : ∃ δ > 0, ∀ y ∈ closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  obtain ⟨K, -, hK⟩ := (f' : V n →ₗ[ℂ] V n).exists_antilipschitzWith (ker_bot_of_det hdet)
  have hev : ∀ᶠ z in 𝓝[≠] (0 : V n), f z ≠ 0 := hf.eventually_ne (c := 0) ⟨K, hK⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, half_pos hε, fun y hy hy0 => ?_⟩
  by_contra hne
  have hyd : dist y 0 < ε := lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hε)
  exact hball hyd hne hy0

theorem coord_ne_of_det {f : V n → V n} (hn : 1 ≤ n) (hdet : (fderiv ℂ f 0).det ≠ 0) :
    ∃ k : Fin n, ¬ (fun z => f z k) =ᶠ[𝓝 0] 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ᶠ z in 𝓝 (0 : V n), ∀ k : Fin n, f z k = 0 := by
    rw [Filter.eventually_all]
    intro k
    exact hcon k
  have hf0 : f =ᶠ[𝓝 0] 0 := by
    filter_upwards [hall] with z hz
    ext k
    simpa using hz k
  have hd : fderiv ℂ f 0 = 0 := by
    rw [hf0.fderiv_eq]
    simp
  apply hdet
  rw [hd]
  have hfr : Module.finrank ℂ (V n) = n := finrank_euclideanSpace_fin
  show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
  rw [ContinuousLinearMap.coe_zero, LinearMap.det_zero, hfr]
  exact zero_pow (by omega)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

def uL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def vL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

theorem cont_uL : Continuous (uL X x1' b1) := by
  unfold uL
  exact continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)

variable {X b1}

theorem mat_uL (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (uL X x1' b1 x) τ = mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ := rfl

private lemma det_mat_ne_zero_of_isOrth {x : Frame X.Ψ r} (ho : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have hg := ho τ
  have e : gram τ.1 X.Gm (mat x τ) =
      (mat x τ).transpose * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hd := congrArg Matrix.det hg
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at hd
  refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
  unfold sgn
  split_ifs <;> norm_num

theorem uL_cpt (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (z : V (nd X)) (b : Frame X.Ψ r) :
    uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b) = rmul (cpt X x1' z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  show mat (uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b)) τ = mat (rmul (cpt X x1' z) b) τ
  rw [mat_uL]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB]

theorem vL_uL (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    vL X x1' b1 (uL X x1' b1 x) = x := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (uL X x1' b1 x)) τ = mat x τ
  rw [e, mat_uL]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.mul_nonsing_inv_cancel_left _ _ hB,
    Matrix.mul_nonsing_inv_cancel_left _ _ hA]

theorem vL_cpt (ho' : IsOrth X x1') (z : V (nd X)) (b : Frame X.Ψ r) :
    vL X x1' b1 (rmul (cpt X x1' z) b) = rmul (cpt X (rmul x1' b1) z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  have e2 : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (rmul (cpt X x1' z) b)) τ = mat (rmul (cpt X (rmul x1' b1) z) b) τ
  rw [e2]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA]

theorem Tset_eq_pre (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    Tset X (rmul x1' b1) ρ = uL X x1' b1 ⁻¹' (ExtFPf.cell D ∩ D.zOf ⁻¹' Metric.ball 0 ρ) := by
  ext x
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    rw [uL_cpt ho' hb1]
    obtain ⟨hΔ, hzz, -⟩ := D.uniq z (hO hz) b hb
    exact ⟨⟨OntoS.dom_rmul X (hO hz) hb, hΔ⟩, by rw [hzz]; exact hz⟩
  · rintro ⟨hcell, hzb⟩
    obtain ⟨-, hbm, e⟩ := D.split _ hcell.1 hcell.2
    refine ⟨⟨D.zOf (uL X x1' b1 x), D.bOf (uL X x1' b1 x)⟩, ⟨hzb, hbm⟩, ?_⟩
    simp only
    rw [← vL_cpt (b1 := b1) ho', ← e, vL_uL ho' hb1]

include D in
theorem isOpen_Tset (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') : IsOpen (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq_pre D ho' hb1 hO]
  exact (D.hz.continuousOn.isOpen_inter_preimage (ExtFPf.isOpen_cell D) Metric.isOpen_ball).preimage
    (cont_uL X b1)

private lemma lact_lact_eq_lact_mul (γ δ : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private lemma lact_one_upper_bounds (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem sat_eq (x1 : Frame X.Ψ r) (ρ : ℝ) :
    {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)} =
      ⋃ γ : X.Γ, lact γ.1⁻¹ ⁻¹' Tset X x1 ρ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Tset, Set.mem_image, Set.mem_prod,
    Prod.exists]
  constructor
  · rintro ⟨γ, hγ, b, hb, z', hz', rfl⟩
    refine ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, ?_⟩
    show _ = lact γ⁻¹ (lact γ _)
    rw [lact_lact_eq_lact_mul, inv_mul_cancel, lact_one_upper_bounds]
  · rintro ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, h⟩
    refine ⟨γ, hγ, b, hb, z', hz', ?_⟩
    have h' : lact γ (lact γ⁻¹ x) = lact γ (rmul (cpt X x1 z') b) := by
      rw [← h]
    rw [lact_lact_eq_lact_mul, mul_inv_cancel, lact_one_upper_bounds] at h'
    exact h'

include D in
theorem isOpen_sat (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
      x = lact γ (rmul (cpt X (rmul x1' b1) z') b)} := by
  rw [sat_eq]
  refine isOpen_iUnion fun γ => ?_
  have hc : Continuous (fun x : Frame X.Ψ r => lact γ.1⁻¹ x) :=
    continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)
  exact (isOpen_Tset D ho' hb1 hO).preimage hc

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end

